import sequtils
import strutils
import parseutils
import strformat
import os
import sets
import posix_utils
import posix
import tables
import times
import lists

import cxx_eval
import cursor

when false: #not defined(release):
  import wave
  type CppStdExcept {.importcpp: "std::exception", header: "<exception>".} = object
  proc what(s: CppStdExcept): cstring {.importcpp: "((char *)#.what())".}

type
  List[T] = DoublyLinkedList[T]

  ElemKind = enum
      IfChain
      IncludeElem
      ImportElem
      ErrorElem
      DefineElem
      PushMacroElem
      PopMacroElem
      LineElem
      ModuleElem
  Conditional = object
    cond: string
    toks: seq[string]
    body: ref seq[Elem]
  Elem = ref object
    case kind: ElemKind
    of IfChain:
      conditionals: seq[Conditional]
      parent: Elem
    of IncludeElem:
      path: string
      next_from: string
    of PushMacroElem, PopMacroElem:
      ppName: string
    of LineElem:
      line: int
      lineFile: string
    of DefineElem:
      name: string
      arguments: seq[string]
      value: string
      toks: seq[string]
      isUndef: bool
      isFunc: bool
    of ErrorElem:
      message: string
    of ImportElem:
      importModule: string
    of ModuleElem:
      moduleName: string
      isExport: bool

  FileScanState = object
    cursor: Cursor
    path: string
    root: seq[Elem]
    curSeq: ptr seq[Elem]
    curIf: Elem
  EvalState = object
    defines: Table[string, Elem #[DefineElem]# ]
    masked: seq[string]
    when false: #not defined(release):
      wave: Wave

converter toCursor(fss: var FileScanState): var Cursor = fss.cursor

proc text(fss: var FileScanState): var string = fss.cursor.text
proc pos(fss: var FileScanState): var int = fss.cursor.pos
proc `text=`(fss: var FileScanState, text: string) =
  fss.cursor.text = text
proc `pos=`(fss: var FileScanState, pos: int) =
  fss.cursor.pos = pos

proc spliceAfterInto[T](src: List[T], pos: DoublyLinkedNode[T], dst: var List[T]): DoublyLinkedNode[T] =
  proc link(a, b: DoublyLinkedNode[T]) =
    if a != nil: a.next = b
    if b != nil: b.prev = a

  if src.head == nil: return pos
  if dst.head == nil:
    dst = src
    return src.tail
  if pos == nil:
    link src.tail, dst.head
    dst.head = src.head
    return src.tail

  link src.tail, pos.next
  link pos, src.head
  if src.tail.next == nil:
    dst.tail = src.tail
  return src.tail

proc replaceInto[T](src: List[T], a, b: DoublyLinkedNode[T], dst: var List[T]): DoublyLinkedNode[T] =
  proc link(a, b: DoublyLinkedNode[T]) =
    if a != nil: a.next = b
    if b != nil: b.prev = a
  let prev = a.prev
  if prev == nil:
    dst.head = b.next
  else:
    link prev, b.next
  if b.next == nil:
    dst.tail = prev

  return src.spliceAfterInto(prev, dst)
    
proc toList[T](src: seq[T]): List[T] =
  for x in src:
    result.append(x)

proc toList1[T](src: T): List[T] =
  result.append(src)

proc print(elem: Elem, depth = 0)
proc print(elems: seq[Elem], depth = 0) =
  if elems.len == 0:
    echo " ".repeat(depth * 4) & "---"
  for elem in elems:
    print(elem, depth)
proc print(elem: Elem, depth = 0) =
  let prefix = " ".repeat(depth * 4)
  case elem.kind
  of IfChain:
    echo &"{prefix}#if_chain"
    for conditional in elem.conditionals:
      echo &"{prefix} {conditional.cond}"
      print(conditional.body[], depth+1)
  of IncludeElem:
    echo &"{prefix}#include {elem.path}"
  of PushMacroElem:
    echo &"{prefix}#push_macro {elem.ppName}"
  of PopMacroElem:
    echo &"{prefix}#pop_macro {elem.ppName}"
  of LineElem:
    echo &"{prefix}#line {elem.line} {elem.lineFile}"
  of DefineElem:
    if elem.isUndef:
      echo &"{prefix}#undef {elem.name}"
    elif elem.isFunc:
      echo &"{prefix}#define {elem.name}({elem.arguments.join(\", \")}) {elem.value}"
    else:
      echo &"{prefix}#define {elem.name} {elem.value}"
  of ErrorElem:
    echo &"{prefix}#error {elem.message}"
  of ImportElem:
    echo &"{prefix}import {elem.importModule}"
  of ModuleElem:
    echo &"{prefix}{elem.isExport} module {elem.moduleName}"

proc makeFileScanState(path: string): FileScanState =
  #result.root.new
  result.path = path
  result.cursor = Cursor(text: "", pos: 0)
  result.curSeq = addr result.root

proc pushCond(fss: var FileScanState, cond: string) =
  fss.curIf[].conditionals.setLen(fss.curIf[].conditionals.len + 1)
  fss.curIf[].conditionals[^1].cond = cond
  var c = Cursor(text:cond)
  fss.curIf[].conditionals[^1].toks = c.tokenize
  fss.curIf[].conditionals[^1].body.new
  fss.curSeq = addr fss.curIf[].conditionals[^1].body[]

proc pushIf(fss: var FileScanState, cond: string) =
  var elem = Elem(kind: IfChain)
  elem.parent = fss.curIf;
  fss.curSeq[] &= elem
  fss.curIf = elem;
  fss.pushCond(cond)

proc popIf(fss: var FileScanState) =
  assert fss.curIf != nil
  let empty = fss.curIf.conditionals.allIt(it.body[].len == 0)
  fss.curIf = fss.curIf.parent;
  assert fss.curIf == nil or fss.curIf.kind == IfChain
  if fss.curIf != nil:
    fss.curSeq = addr fss.curIf.conditionals[^1].body[]
  else:
    fss.curSeq = addr fss.root
  if empty:
    discard
    discard fss.curSeq[].pop

proc handleInclude(state: var EvalState, rest: string, next_from="")

proc parseDefine(directive: string): Elem =
  var cursor = Cursor(text:directive)
  cursor.skipPastWhitespaceAndComments()
  let name = cursor.parseIdent()
  # no whitespace skipping here!
  if cursor.pos == cursor.text.len or cursor.cur != '(':
    cursor.skipPastWhitespaceAndComments()
    if cursor[0] == '=': cursor.pos.dec
    var tc = Cursor(text: cursor.text[cursor.pos..^1])
    return Elem(kind: DefineElem, name: name, value: tc.text, toks: tc.tokenize)
  cursor.pos.inc
  cursor.skipPastWhitespaceAndComments()
  var args: seq[string] = @[]
  if cursor.cur == ')':
    cursor.pos.inc
  else:
    while true:
      cursor.skipPastWhitespaceAndComments()
      # TODO \newline support
      var arg = cursor.text.parseIdent(start=cursor.pos)
      if arg.len == 0:
        assert cursor.text[cursor.pos..cursor.pos+2] == "..."
        arg = "..."
      else:
        assert arg.len > 0
      cursor.pos += arg.len
      cursor.skipPastWhitespaceAndComments()
      cursor.pos.inc
      args &= arg
      if cursor.text[cursor.pos-1] == ')': break
      assert cursor.text[cursor.pos-1] == ','
  var tc = Cursor(text: cursor.text[cursor.pos..^1])
  return Elem(kind: DefineElem, name: name, isFunc: true, arguments: args,
              value: tc.text, toks: tc.tokenize)

var pragmaOnceCount = 0
proc handleDirective(fss: var FileScanState; directive, rest: string) =
  case directive:
  of "if": fss.pushIf rest
  of "ifdef": fss.pushIf &"defined({rest})"
  of "ifndef": fss.pushIf &"!defined({rest})"
  of "elif": fss.pushCond rest
  of "else": fss.pushCond "true"
  of "endif": fss.popIf()

  of "warning": discard # meh
  of "error": fss.curSeq[] &= Elem(kind:ErrorElem, message: rest)
  of "define": fss.curSeq[] &= parseDefine(rest)
  of "undef": fss.curSeq[] &= Elem(kind:DefineElem, name: rest, isUndef: true)

  of "pragma":
    if rest.strip != "once": return
    let myId = &"__PRAG_ONCE_{pragmaOnceCount}"
    fss.pushIf &"!defined({myId})"
    fss.curSeq[] &= Elem(kind:DefineElem, name: myId)

  of "include_next":
    fss.curSeq[] &= Elem(kind:IncludeElem, path: rest, next_from: fss.path)
    #handleInclude(rest, fss.path)
  of "include":
    fss.curSeq[] &= Elem(kind:IncludeElem, path: rest)
    #handleInclude(rest)
  else:
    echo &"unknown directive #{directive} {rest}"
    discard

proc handleHash(fss: var FileScanState) =
  assert fss.text[fss.pos] == '#'
  fss.pos.inc # skip the #
  for i in countdown(fss.pos-2, 0):
    if fss.text[i] == '\n':
      if i != 0 and fss.text[i-1] == '\\': continue # :(
      break
    elif fss.text[i] in (Whitespace - {'\n'}):
      continue
    else:
      echo &"why is a # following a {fss.text[i]}"
      return

  fss.skipPastWhitespaceAndComments()
  if fss.text[fss.pos] in {'\n', '0'..'9'}:
    return
  let directive = fss.cursor.parseIdent
  fss.skipPastWhitespaceAndComments()
  let restStart = fss.pos
  let rest = fss.cursor.filterCommentsToEndOfLine()
  #print fss.root
  #echo &"#{directive} {rest}"
  fss.handleDirective(directive, rest)

proc scanTopLevel(fss: var FileScanState) =
  const intersting = {'/', '#', '"'}
  fss.pos += fss.text.skipUntil(intersting, start=fss.pos)
  while fss.pos < fss.text.len:
    let start = fss.pos
    let cur = fss.text[fss.pos]
    if cur == '/':
      let next = fss.text[fss.pos+1]
      if next == '/' or next == '*':
        fss.skipPastWhitespaceAndComments
      else:
        fss.pos += 1
    elif cur == '"':
      fss.pos += 1
      if fss.pos != 1 and fss.text[fss.pos-2] == 'R':
        fss.skipPastEndOfRawString
      elif fss.pos != 1 and fss.text[fss.pos-2] != '\'': # '"' doesn't open a string!
        fss.skipPastEndOfSimpleString
    else:
      assert cur == '#'
      fss.handleHash
    fss.pos += fss.text.skipUntil(intersting, start=fss.pos)
    #echo &"skipped {fss.pos - start} bytes from {cur}"



proc parseByteWise(fss: var FileScanState, isRoot = false) =
  echo &"\nstarting on {fss.path}"
  fss.text = readFile(fss.path)
  const prelude = slurp("clang_prelude.h")
  if isRoot: fss.text = prelude & fss.text
  fss.scanTopLevel

let searchPath = @[
  "/usr/bin/../include/c++/v1",
  "/usr/local/include",
  "/usr/lib/clang/10.0.0/include",
  "/usr/include",
  "./src",
  "./build/prefix/include",
  "./build/prefix/include/bsoncxx/v_noabi",
  "./build/prefix/include/mongocxx/v_noabi",
  "/home/mstearn/realm-core/src/",
  "/home/mstearn/realm-core/src/realm",
  "/home/mstearn/realm-core/src/realm/parser",
  "/home/mstearn/realm-core/build/src/",
]
let quotePath = @[
  "."
] & searchPath

proc findInclude(isQuote:bool, partial: string, next_from: string): string =
  let
    search = if isQuote: quotePath else: searchPath
    checkNextFrom = next_from.len != 0
    curParent = if checkNextFrom: next_from.absolutePath.parentDir else: ""

  var foundCur = not checkNextFrom
  for prefix in search:
    let path = prefix / partial
    if path.fileExists:
      if checkNextFrom:
        if path.absolutePath.parentDir == curParent:
          #echo &"skipping {path} for include_next for {next_from}"
          continue
      if checkNextFrom:
        #echo &"accepted {path} for include_next for {next_from}"
        discard
      return path
  echo &"can't find file for {partial} from {next_from}"
  return ""

var
  files: Table[string, seq[Elem]]
  filesQueued: HashSet[string]
  fileQueue = @[paramStr(1)]

proc expandDefined(state: EvalState, c: var Cursor): string =
  c.skipPastWhitespaceAndComments()
  let isParens = c.cur == '('
  if isParens:
    c.pos.inc
    c.skipPastWhitespaceAndComments()
  let ident = c.parseIdent
  c.skipPastWhitespaceAndComments()
  if isParens:
    assert c.cur == ')'
    c.pos.inc
  #echo &"defined({ident}): {$(ident in state.defines)}"
  return $(ident in state.defines)

proc expand(state: var EvalState, input: List[string], macroName = "",  args = Table[string, seq[string]]()): List[string]
proc expand(state: var EvalState, input: seq[string], macroName = "",  args = Table[string, seq[string]]()): List[string] =
  return state.expand(input.toList(), macroName=macroName,  args=args)
proc expand(state: var EvalState, input: string, macroName = "",  args = Table[string, seq[string]]()): List[string] =
  var c = Cursor(text: input)
  return state.expand(c.tokenize, macroName=macroName, args=args)

proc parseMacroArgs(cur: var DoublyLinkedNode[string], variadicLen: int): seq[seq[string]] =
  while cur.value != ")":
    if result.len != variadicLen:
      result &= @[]
    var nesting = 0
    while nesting != 0 or cur.value notin [")", ","]:
      if cur.value == "(": nesting.inc
      elif nesting > 0 and cur.value == ")": nesting.dec
      result[^1] &= cur.value
      cur = cur.next
      assert cur != nil
      if cur == nil: return # XXX
    if cur.value == ",":
      cur = cur.next


func nextSkipWS(node: DoublyLinkedNode[string]): DoublyLinkedNode[string] =
  if node == nil: return nil
  result = node.next
  while result != nil:
    if (result.value != " "): return
    result = result.next
func nextSkipWSStr(node: DoublyLinkedNode[string]): string =
  let x = node.nextSkipWS
  return if x == nil: "" else: x.value
func prevSkipWS(node: DoublyLinkedNode[string]): DoublyLinkedNode[string] =
  if node == nil: return nil
  result = node.prev
  while result != nil:
    if (result.value != " "): return
    result = result.prev
func prevSkipWSStr(node: DoublyLinkedNode[string]): string =
  let x = node.prevSkipWS
  return if x == nil: "" else: x.value

proc trimWS(input: List[string]): List[string] =
  result = input
  while result.head != nil and result.head.value == " ": result.remove(result.head)
  while result.tail != nil and result.tail.value == " ": result.remove(result.tail)

var callCount = 0
proc expand(state: var EvalState, input: List[string], macroName = "", args = Table[string, seq[string]]()): List[string] =
  const printing  = false
  let call = if printing: $callCount & "::   " else : ""
  callCount.inc

  result = input
  if printing: echo call, macroName, ' ', result
  defer:
    if printing:  echo call, result

  let evaledArgs = toSeq(args.pairs).mapIt((it[0], state.expand(it[1]).trimWS.toSeq)).toTable
  if printing: echo call, evaledArgs
  var cur = input.head
  if args.len != 0:
    while cur != nil:
      if cur.value == "__VA_ARGS__": assert cur.value in args
      if cur.value in args:
        let next = cur.nextSkipWSStr
        let prev = cur.prevSkipWSStr
        if next == "##" or prev == "##" or prev == "#":
          # XXX for ## shouldn't join tokens.
          if prev == "#":
            cur.value = evaledArgs[cur.value].join().strip()
            cur.value = &"\"{cur.value}\""
            while true:
              let stop = cur.prev.value == "#"
              result.remove(cur.prev)
              if stop: break
          else:
            cur.value = args[cur.value].filterIt(it.len != 0 and it != " ").join()
        else:
          let evaled = evaledArgs[cur.value]
          if evaled.len == 0:
            cur.value = ""
          else:
            cur = evaled.toList().replaceInto(cur, cur, result)
      cur = cur.next
  cur = input.head
  while cur != nil:
    if cur.value == "#":
      echo "XXX: ",  result
      assert cur.value != "#"
    if cur.value == "##":
      let next = cur.nextSkipWS
      let prev = cur.prevSkipWS
      cur.value = prev.value & next.value
      cur = List[string](head: cur, tail: cur).replaceInto(prev, next, result)
    cur = cur.next

  if macroName.len != 0: state.masked &= macroName

  cur = input.head
  while cur != nil:
    var didExpand = false
    let mayBeFunc = cur.nextSkipWS != nil and cur.nextSkipWS.value == "("
    if cur.value in state.defines and cur.value notin state.masked:
      let def = state.defines[cur.value]
      assert not def.isUndef
      if not def.isFunc:
        cur = state.expand(def.toks, macroName=def.name).replaceInto(cur, cur, result)
        didExpand = true
      elif mayBeFunc:
        let start = cur
        let variadicLen =
          if def.arguments.len != 0 and def.arguments[^1] == "...": def.arguments.len
          else: -1
        cur = cur.nextSkipWS.next
        let rawArgs = cur.parseMacroArgs(variadicLen)
        doAssert def.arguments.len == rawArgs.len

        var callArgs: Table[string, seq[string]]
        for i, name in def.arguments:
          callArgs[if name == "...": "__VA_ARGS__" else: name] = rawArgs[i]
        
        #echo def.value
        #echo def.value.tokenize
        #echo def.toks
        #assert def.toks == def.value.tokenize
        cur = state.expand(def.toks, macroName=def.name, args=callArgs).replaceInto(start, cur, result)
        didExpand = true
    else:
      let start = cur
      case cur.value:
      of "defined":
        var name: string
        if mayBeFunc:
          cur = cur.nextSkipWS.nextSkipWS
          name = cur.value
          cur = cur.nextSkipWS
          doAssert cur.value == ")"
        else:
          cur = cur.nextSkipWS
          name = cur.value
        let res = if name in state.defines: "1" else: "0"
        cur = res.toList1.replaceInto(start, cur, result)
        didExpand = true
      of "__has_feature":
        if mayBeFunc:
          cur = cur.nextSkipWS.nextSkipWS
          let name = cur.value
          cur = cur.nextSkipWS
          doAssert cur.value == ")"
          const features = ["XXX"] # TODO
          let res = if name in features: "1" else: "0"
          cur = res.toList1.replaceInto(start, cur, result)
          didExpand = true
    #echo cur.value
    #assert cur.value.cstring[0] notin IdentStartChars or cur.value in ["true", "false"]
    if not didExpand:
      cur = cur.nextSkipWS
  
  if macroName.len != 0: discard state.masked.pop



proc walk(state: var EvalState, e: Elem)
proc walk(state: var EvalState, se: seq[Elem]) =
  for e in se:
    state.walk e

proc macroToWave(elem: Elem): string =
  assert not elem.isUndef
  if elem.isFunc:
    return &"{elem.name}({elem.arguments.join(\", \")})={elem.value}"
  else:
    return &"{elem.name}={elem.value}"

proc getMacros(state: EvalState): seq[string] =
  for name, elem in state.defines:
    if elem.isUndef: continue
    result &= elem.macroToWave

proc walk(state: var EvalState, e: Elem) =
  case e.kind:
  of IfChain:
    for cond in e.conditionals:
      #if state.getMacros.evalCPP(cond.cond):
      if false:
        #echo cond.cond
        discard
        discard state.expand(cond.cond)
        #echo ""
      var expanded = state.expand(cond.toks).toSeq.filterIt(it != " ")
      expanded.shallow
      let res = expanded.eval
      when false: #not defined(release):
        try:
          let waveRes = state.wave.eval(cond.cond)
          if res != waveRes:
            if "UCHAR_MAX" in state.defines:
              echo state.defines["__SCHAR_MAX__"].value
            echo cond.cond
            echo expanded
            echo res
            echo waveRes
            let ignore = [
              "__STDC_VERSION__",
              "__WAVE__",
            ].anyIt(it in cond.cond)
            assert ignore or res == waveRes
        except CppStdExcept as e:
          echo &"ignoring cpp exception: {e.what()}"
      if res:
        state.walk cond.body[]
        break
  of DefineElem:
    if e.isUndef:
      state.defines.del e.name
      #when not defined(release): state.wave.undefMacro e.name
    else:
      when false: #not defined(release):
        if e.name in state.defines:
          discard
          state.wave.undefMacro e.name
      state.defines[e.name] = e
      when false: #not defined(release):
        if not (e.name[0] == '_' and e.name in [
          "__STDC__",
          "__STDC_HOSTED__",
          "__cplusplus",
          ]):
          state.wave.defineMacro e.macroToWave
  of IncludeElem:
    state.handleInclude(e.path, e.next_from)
  else: discard

proc handleInclude(state: var EvalState, rest: string, next_from="") =
  var close: int
  case rest[0]:
  of '"': close = rest.find('"', start=1)
  of '<': close = rest.find('>', start=1)
  else:
    let expanded = state.expand(rest).toSeq.join().strip()
    echo &"wtf include {rest} => {expanded}"
    assert expanded[0] in {'<', '"'}
    state.handleInclude(expanded, next_from)
    return
  let path = findInclude(rest[0] == '"', rest[1..<close], next_from)
  if path.len == 0: return
  if path notin files:
    var fss = makeFileScanState(path)
    fss.parseByteWise
    files[path] = fss.root
  state.walk files[path]

for _ in 1..10:
  #GC_enableMarkAndSweep()
  #GC_fullCollect()
  #GC_disableMarkAndSweep()
  filesQueued.clear()
  fileQueue = @[paramStr(1)]
  while fileQueue.len != 0:
    let file = fileQueue.pop
    var fss = makeFileScanState(file)
    fss.parseByteWise(isRoot=true)
    #print fss.root
    block:
      let start = getTime()
      var evalState: EvalState
      when false: #not defined(release):
        evalState.wave = makeWave()
      evalState.walk fss.root
      echo getTime() - start
    let start = getTime()
    if true: break
    const rep = 10
    for _ in 1..rep:
      var evalState: EvalState
      when false: #not defined(release):
        evalState.wave = makeWave()
      evalState.walk fss.root
    echo (getTime() - start) div rep
