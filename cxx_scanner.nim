import patty
import std/strutils
import sequtils
import strutils
import parseutils
import strformat
import os
import sets
import posix_utils
import posix

type
  Cursor = object
    text: string
    pos: int

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
      name, arguments, value: string
      isUndef: bool
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

converter toCursor(fss: var FileScanState): var Cursor = fss.cursor
proc text(fss: var FileScanState): var string = fss.cursor.text
proc pos(fss: var FileScanState): var int = fss.cursor.pos

proc `text=`(fss: var FileScanState, text: string) =
  fss.cursor.text = text
proc `pos=`(fss: var FileScanState, pos: int) =
  fss.cursor.pos = pos

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
    else:
      echo &"{prefix}#define {elem.name}{elem.arguments} {elem.value}"
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

proc handleInclude(rest: string, next_from="")
proc skipPastWhitespaceAndComments(cursor: var Cursor)

proc skipPastEndOfLine(cursor: var Cursor) =
  while cursor.pos < cursor.text.len:
    # position after next \n
    cursor.pos += cursor.text.skipUntil('\n', start=cursor.pos) + 1
    case cursor.text[cursor.pos-2] # before the \n
    of '\\': continue
    of '\r':
      if cursor.text[cursor.pos-3] == '\\':
        continue
    else: discard
    return

proc skipPastEndOfRawString(cursor: var Cursor) =
  assert cursor.text[cursor.pos-2 ..< cursor.pos] == "R\""
  # [lex.string] calls these d-char. I guess d is for delimiter?
  const dchars = AllChars - {' ', '(', ')', '\\', '\t', '\v', '\r', '\n'}
  let dstart = cursor.pos
  cursor.pos += cursor.text.skipWhile(dchars, start=cursor.pos)
  assert cursor.text[cursor.pos] == '('
  let strEnd = &"){cursor.text[dstart..<cursor.pos]}\""
  cursor.pos = cursor.text.find(strEnd, start=cursor.pos+1) + strEnd.len
  #echo cursor.text[dstart-2 ..< cursor.pos]


proc skipPastEndOfSimpleString(cursor: var Cursor) =
  while cursor.pos < cursor.text.len:
    # position after next "
    cursor.pos += cursor.text.skipUntil('"', start=cursor.pos) + 1
    if cursor.text[cursor.pos-2] == '\\': # before the "
      var count = 1
      for i in countdown(cursor.pos-3, 0):
        if cursor.text[i] == '\\':
          count.inc
      if count mod 2 == 1: # an odd number of \ escapes the "
        continue
    return

proc skipPastEndOfComment(cursor: var Cursor) =
  when false:
    while cursor.pos < cursor.text.len:
      # position after next / (which should be less likely than '*')
      cursor.pos += cursor.text.skipUntil('/', start=cursor.pos) + 1
      if cursor.text[cursor.pos-3] == '*': # before the /
        return
      cursor.pos += 1 # on / so can't be on end of */ sequence
  else:
    cursor.pos = cursor.text.find("*/", start=cursor.pos) + 2


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
  of "define": fss.curSeq[] &= Elem(kind:DefineElem, name: rest) # TODO args and such
  of "undef": fss.curSeq[] &= Elem(kind:DefineElem, name: rest, isUndef: true)

  of "pragma": discard # TODO

  of "include_next":
    fss.curSeq[] &= Elem(kind:IncludeElem, path: rest, next_from: fss.path)
    handleInclude(rest, fss.path)
  of "include":
    fss.curSeq[] &= Elem(kind:IncludeElem, path: rest)
    handleInclude(rest)
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
  if fss.text[fss.pos] == '\n':
    return # some boost headers have invalid (but accepted) empty directives
  let directive = fss.text.parseIdent(start=fss.pos)
  fss.pos += directive.len
  let restStart = fss.pos
  fss.skipPastEndOfLine()
  let rest = fss.text[restStart..<fss.pos].strip.multiReplace(("\\\r\n",""), ("\\\n", ""))
  #print fss.root
  #echo &"#{directive} {rest}"
  fss.handleDirective(directive, rest)

proc skipPastWhitespaceAndComments(cursor: var Cursor) =
  while cursor.pos < cursor.text.len:
    let start = cursor.pos
    cursor.pos += cursor.text.skipWhile(Whitespace - {'\n'}, start=cursor.pos)
    if cursor.text[cursor.pos] == '/':
      let next = cursor.text[cursor.pos+1]
      if next == '/':
        cursor.skipPastEndOfLine
        cursor.pos.dec
      elif next == '*':
        cursor.pos += 2 # skip /*
        cursor.skipPastEndOfComment
    if cursor.pos == start: return # done skipping

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



proc parseByteWise(fss: var FileScanState) =
  fss.text = readFile(fss.path)
  fss.scanTopLevel

proc parseLineWise(fss: var FileScanState) =
  for line in readFile(fss.path).splitLines(keepEol=true).filterIt(it.len != 0 and it[0] == '#'):
    let split = line[1..^1].strip().split(maxsplit=1)
    fss.handleDirective(split[0], if split.len > 1: split[1] else: "")
    
let searchPath = @[
  "/usr/bin/../include/c++/v1",
  "/usr/local/include",
  "/usr/lib/clang/8.0.1/include",
  "/usr/include",
]
let quotePath = @[
  "."
] & searchPath

proc findInclude(isQuote:bool, partial: string, next_from: string): string =
  let
    search = if isQuote: quotePath else: searchPath
    checkNextFrom = next_from.len != 0
    curStat = if checkNextFrom: next_from.stat else: Stat()

  var foundCur = not checkNextFrom
  for prefix in search:
    let path = prefix / partial
    if path.fileExists:
      if not foundCur:
        let pathStat = path.stat
        if pathStat.st_dev == curStat.st_dev and pathStat.st_ino == curStat.st_ino:
          foundCur = true
        #echo &"skipping {path} for include_next for {next_from}"
        continue
      if checkNextFrom:
        #echo &"accepted {path} for include_next for {next_from}"
        discard
      return path
  #echo &"can't find file for {partial} from {next_from}"
  return ""

var
  filesQueued: HashSet[string]
  fileQueue = @[paramStr(1)]

proc handleInclude(rest: string, next_from="") =
  var close: int
  case rest[0]:
  of '"': close = rest.find('"', start=1)
  of '<': close = rest.find('>', start=1)
  else:
    echo &"wtf include {rest}"
    return
  let path = findInclude(rest[0] == '"', rest[1..<close], next_from)
  if path.len != 0 and not filesQueued.containsOrIncl(path):
    fileQueue &= path

proc walk(e: Elem)
proc walk(se: seq[Elem]) =
  for e in se:
    e.walk

proc walk(e: Elem) =
  case e.kind:
  of IfChain:
    for cond in e.conditionals:
      echo cond.cond
      cond.body[].walk
  else: discard

for _ in 1..1:
  filesQueued.clear()
  fileQueue = @[paramStr(1)]
  while fileQueue.len != 0:
    let file = fileQueue.pop
    echo &"\nstarting on {file}"
    var fss = makeFileScanState(file)
    if true:
      fss.parseByteWise
    else:
      fss.parseLineWise
    #print fss.root
    #walk fss.root


