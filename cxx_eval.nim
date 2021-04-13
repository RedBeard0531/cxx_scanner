import cursor
import strutils
import strformat
import strtabs
import sequtils

var disarmCount = 0

template assert(cond: typed): void =
  if not cond:
    echo c
    system.assert cond

template doAssert(cond: typed): void =
  if not cond:
    echo c
    system.doAssert cond

template maybeAssert(x: untyped) =
  if disarmCount == 0:
    assert x

type Res = tuple[val: int, unsigned: bool]

template binOp(op, name: untyped): untyped =
  func name(l, r: Res): Res =
    if l.unsigned or r.unsigned:
      (int(op(l.val.uint, r.val.uint)), true)
    else:
      (op(l.val, r.val), false)

template binOp(op: untyped): untyped = binOp op, op

template relOp(op: untyped): untyped =
  func op(l, r: Res): Res =
    if l.unsigned or r.unsigned:
      (int op(l.val.uint, r.val.uint), true)
    else:
      (int op(l.val, r.val), false)

func `==`(r: Res, i: int): Res = (int r.val == i, false)
func `and`(r: Res, other: bool): Res = (int(r.val != 0 and other), false)
func `or`(r: Res, other: bool): Res = (int(r.val != 0 or other), false)
func `not`(r: Res): Res = (not r.val, r.unsigned)
func `+`(r: Res): Res = (+ r.val, r.unsigned)
func `-`(r: Res): Res = (- r.val, r.unsigned)
binOp `+`
binOp `-`
binOp `*`
binOp `div`
binOp `mod`
binOp `shl`
binOp `shr`
binOp `and`, name=bitAnd
binOp `or`, name=bitOr
binOp `xor`
binOp cmp

relOp `<`
relOp `<=`
relOp `>`
relOp `>=`
relOp `==`
relOp `!=`

proc evalAssignment(c: var TokCursor): Res
proc evalExpr(c: var TokCursor): Res

proc evalLiteral(c: var TokCursor): Res =
  #defer: echo "lit: ", result, ' ', c[0]
  case c[0]:
  of "": assert false
  of "true": return (1, false)
  of "false": return (0, false)
  of "L'\\0'": return (0, false)
  of "'\\0'": return (0, false)

  if c[0][0] in Digits:
    if c[0][^1] == 'u':
      result = (c[0][0 ..< ^1].parseUInt.int, true)
    else:
      result = (c[0].parseInt, false)
  elif c[0][0] in IdentStartChars:
    #when not defined(release): echo &"Reading undefined macro {c[0]}"
    c.pos.inc
    return (0, false)
  else:
    maybeAssert c[0][0] in Digits
  c.pos.inc

proc evalCast(c: var TokCursor): Res =
  #defer: echo "cast: ", result, ' ', c[0]
  case c[0]:
  of "!":
    c.pos.inc
    return c.evalCast == 0
  of "+":
    c.pos.inc
    return + c.evalCast
  of "-":
    c.pos.inc
    return - c.evalCast
  of "~":
    c.pos.inc
    return not c.evalCast
  of "(":
    c.pos.inc
    result = c.evalExpr
    assert c[0] == ")"
    c.pos.inc
  #of "*", "&", "++", "--":
  else:
    return c.evalLiteral

proc evalPM(c: var TokCursor): Res =
  #defer: echo "PM: ", result, c[0]
  result = c.evalCast
  maybeAssert c[0] notin [".*", "->*"]
  
proc evalMult(c: var TokCursor): Res =
  #defer: echo "Mul: ", result, c[0]
  result = c.evalPM
  while c[0].len == 1 and c[0][0] in {'*', '/', '%'}:
    c.pos.inc
    case c.prev[0]:
    of '*': result = result * c.evalPM
    of '/': result = result.div c.evalPM
    of '%': result = result.mod c.evalPM
    else: assert false

proc evalAdditive(c: var TokCursor): Res =
  #defer: echo &"add: {result} ", c[0]
  result = c.evalMult
  while c[0].len == 1 and c[0][0] in {'+', '-'}:
    c.pos.inc
    case c.prev[0]:
    of '+': result = result + c.evalMult
    of '-': result = result - c.evalMult
    else: assert false

proc evalShift(c: var TokCursor): Res =
  #defer: echo &"shif: {result} ", c[0]
  result = c.evalAdditive
  while c[0].len == 2 and c[0] in ["<<", ">>"]:
    c.pos.inc
    case c.prev:
    of "<<": result = result.shl c.evalAdditive
    of ">>": result = result.shr c.evalAdditive
    else: assert false

proc evalCompare(c: var TokCursor): Res =
  #defer: echo &"comp: {result} ", c[0]
  result = c.evalShift
  while c[0] == "<=>":
    c.pos.inc
    result = result.cmp c.evalShift

proc evalRelational(c: var TokCursor): Res =
  #defer: echo &"rel: {result} ", c[0]
  result = c.evalCompare
  while c[0] in ["<=", ">=", "<", ">"]:
    c.pos.inc
    case c.prev:
    of "<": result = result < c.evalCompare
    of ">": result = result > c.evalCompare
    of "<=": result = result <= c.evalCompare
    of ">=": result = result >= c.evalCompare
    else: assert false

proc evalEquality(c: var TokCursor): Res =
  #defer: echo &"eq: {result} ", c[0]
  result = c.evalRelational
  while c[0].len == 2 and c[0] in ["==", "!="]:
    c.pos.inc
    case c.prev:
    of "==": result = Res result == c.evalRelational
    of "!=": result = Res result != c.evalRelational
    else: assert false

proc evalAnd(c: var TokCursor): Res =
  #defer: echo &"bitand: {result} ", c[0]
  result = c.evalEquality
  while c[0] == "&":
    c.pos.inc
    result = result.bitAnd c.evalEquality

proc evalExclusiveOr(c: var TokCursor): Res =
  #defer: echo &"xor: {result} ", c[0]
  result = c.evalAnd
  while c[0] == "^":
    c.pos.inc
    result = result xor c.evalAnd

proc evalInclusiveOr(c: var TokCursor): Res =
  #defer: echo &"bitor: {result} ", c[0]
  result = c.evalExclusiveOr
  while c[0] == "|":
    c.pos.inc
    result = result.bitOr c.evalExclusiveOr

proc evalLogicalAnd(c: var TokCursor): Res =
  #defer: echo &"an:d {result} ", c[0]
  result = c.evalInclusiveOr
  while c[0] == "&&":
    c.pos.inc
    if result.val == 0: disarmCount.inc
    let other = c.evalInclusiveOr.val != 0
    if result.val == 0: disarmCount.dec
    result = result and other

proc evalLogicalOr(c: var TokCursor): Res =
  #defer: echo &"or: {result} ", c[0]
  result = c.evalLogicalAnd
  while c[0] == "||":
    if result.val != 0: disarmCount.inc
    c.pos.inc
    let other = c.evalLogicalAnd.val != 0
    if result.val != 0: disarmCount.dec
    result = result or other

proc evalConditional(c: var TokCursor): Res =
  #defer: echo &"cond: {result} ", c[0]
  let cond = c.evalLogicalOr
  if c[0] != "?": return cond

  c.pos.inc
  let isTrue = cond.val != 0
  let isFalse = cond.val == 0

  if isFalse: disarmCount.inc
  let trueSide = c.evalExpr
  if isFalse: disarmCount.dec

  assert c[0] == ":"
  c.pos.inc

  if isTrue: disarmCount.inc
  let falseSide = c.evalAssignment
  if isTrue: disarmCount.dec

  return if isTrue: trueSide else: falseSide

proc evalAssignment(c: var TokCursor): Res =
  result = c.evalConditional
  assert c[0] notin ["=", "*=", "/=", "%=", "+=", "-=", ">>=", "<<=", "&=", "^=", "|="]

proc evalExpr(c: var TokCursor): Res =
  result = c.evalAssignment
  while c[0] == ",":
    c.pos.inc
    discard result
    result = c.evalAssignment


let altTokens = {
  "and": "&&",
  "or": "||",
  "xor": "^",
  "not": "!",
  "bitand": "&",
  "bitor": "|",
  "compl": "~",
  "and_eq": "&=",
  "or_eq": "|=",
  "xor_eq": "^=",
  "not_eq": "!=",
}.newStringTable

proc eval*(s: seq[string]): bool =
  #echo "-------"
  #echo s
  var c = TokCursor(text: s.mapIt(if it in altTokens: altTokens[it] else: it))
  return c.evalConditional.val != 0

