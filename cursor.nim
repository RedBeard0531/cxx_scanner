import strutils
import parseutils
import strformat

type
  Cursor* = object
    text*: string
    pos*: int

  TokCursor* = object
    text*: seq[string]
    pos*: int

  AnyCursor = Cursor | TokCursor

  
{.push inline.}

func `[]`*(c: AnyCursor, offset: int): auto =
  let i = offset + c.pos
  if i < 0 or i > c.text.high:
    when c is Cursor:
      return '\0'
    else:
      return ""
  return c.text[i]

func cur*(c: AnyCursor): auto = c.text[c.pos]
func next*(c: AnyCursor): auto = c[1]
func prev*(c: AnyCursor): auto = c[-1]
func `$`*(c: Cursor): string = c.text & '\n' & " ".repeat(c.pos) & '^'
func more*(c: AnyCursor): bool = c.pos < c.text.high
func atEnd*(c: AnyCursor): bool = c.pos == c.text.len
func notAtEnd*(c: AnyCursor): bool = not c.atEnd

{.pop.}

proc skipPastWhitespaceAndComments*(cursor: var Cursor)

proc skipPastEndOfLine*(cursor: var Cursor) =
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

proc skipPastEndOfRawString*(cursor: var Cursor) =
  assert cursor.text[cursor.pos-2 ..< cursor.pos] == "R\""
  # [lex.string] calls these d-char. I guess d is for delimiter?
  const dchars = AllChars - {' ', '(', ')', '\\', '\t', '\v', '\r', '\n'}
  let dstart = cursor.pos
  cursor.pos += cursor.text.skipWhile(dchars, start=cursor.pos)
  assert cursor.text[cursor.pos] == '('
  let strEnd = &"){cursor.text[dstart..<cursor.pos]}\""
  cursor.pos = cursor.text.find(strEnd, start=cursor.pos+1) + strEnd.len
  #echo cursor.text[dstart-2 ..< cursor.pos]


proc skipPastEndOfSimpleString*(cursor: var Cursor) =
  while cursor.pos < cursor.text.len:
    # position after next "
    cursor.pos += cursor.text.skipUntil('"', start=cursor.pos) + 1
    if cursor.text[cursor.pos-2] == '\\': # before the "
      var count = 1
      for i in countdown(cursor.pos-3, 0):
        if cursor.text[i] == '\\': count.inc
        else: break
      if count mod 2 == 1: # an odd number of \ escapes the "
        continue
    return

proc skipPastEndOfComment*(cursor: var Cursor) =
  when false:
    while cursor.pos < cursor.text.len:
      # position after next / (which should be less likely than '*')
      cursor.pos += cursor.text.skipUntil('/', start=cursor.pos) + 1
      if cursor.text[cursor.pos-3] == '*': # before the /
        return
      cursor.pos += 1 # on / so can't be on end of */ sequence
  else:
    cursor.pos = cursor.text.find("*/", start=cursor.pos) + 2

proc filterCommentsToEndOfLine*(c: var Cursor): string =
  var lastStart = c.pos
  const intersting = {'/', '"', '\n'}
  c.pos += c.text.skipUntil(intersting, start=c.pos)
  while c.pos < c.text.len:
    let start = c.pos
    if c.cur == '/':
      if c.next == '/' or c.next == '*':
        result &= c.text[lastStart..<c.pos]
        c.skipPastWhitespaceAndComments
        result &= ' '
        lastStart = c.pos
      else:
        c.pos += 1
    elif c.cur == '"':
      c.pos += 1
      if c[-2] == 'R':
        c.skipPastEndOfRawString
      elif c[-2] != '\'': # '"' doesn't open a string!
        c.skipPastEndOfSimpleString
    else:
      assert c.cur == '\n'
      case c.text[c.pos-1] # before the \n
      of '\\':
        result &= c.text[lastStart..<c.pos-1]
        c.pos.inc
        lastStart = c.pos
      of '\r':
        if c.text[c.pos-2] == '\\':
          result &= c.text[lastStart..<c.pos-2]
          c.pos.inc
          lastStart = c.pos
      else:
        break
    c.pos += c.text.skipUntil(intersting, start=c.pos)
  result &= c.text[lastStart..<min(c.pos, c.text.len)]

proc skipPastWhitespaceAndComments*(cursor: var Cursor) =
  while cursor.pos < cursor.text.len:
    let start = cursor.pos
    cursor.pos += cursor.text.skipWhile(Whitespace - {'\n'}, start=cursor.pos)
    if cursor.pos == cursor.text.len: return
    if cursor.text[cursor.pos] == '/':
      let next = cursor.text[cursor.pos+1]
      if next == '/':
        cursor.skipPastEndOfLine
        cursor.pos.dec
      elif next == '*':
        cursor.pos += 2 # skip /*
        cursor.skipPastEndOfComment
    if cursor.pos == start: return # done skipping

proc consumeOperator(c: var Cursor, opers: static seq[string]): string {.inline.} =
  for op in opers:
    assert c.cur == op[0]
    case op.len:
    of 3:
      if c[1] == op[1] and c[2] == op[2]:
        c.pos += 3
        return op
    of 2:
      if c[1] == op[1]:
        c.pos += 2
        return op
    of 1:
      c.pos += 1
      return op
    else: assert op.len <= 3


proc parseIdent*(c: var Cursor): string =
  result &= c.text.parseIdent(start=c.pos)
  c.pos += result.len
  assert result.len > 0
  while c[0] == '/' and c[1] == '\n':
    c.pos += 2
    result &= c.text.parseIdent(start=c.pos)
    c.pos += result.len

proc consumeNumber(c: var Cursor, base: static uint): string =
  var num = 0u64
  c.pos -= 1
  try:
    while true:
      c.pos.inc
      case c[0]:
      of '\'': discard
      of Digits:
        num *= base
        let part = c.cur.ord - '0'.ord
        assert part < base
        num += part.uint64
      of 'a'..'f':
        num *= base
        let part = 10 + c.cur.ord - 'a'.ord
        assert part < base
        num += part.uint64
      of 'A'..'F':
        num *= base
        let part = 10 + c.cur.ord - 'A'.ord
        assert part < base
        num += part.uint64
      else:
        result = $num
        while c[0] in {'u', 'U', 'l', 'L'}:
          if c.cur in {'u', 'U'}: result &= 'u'
          c.pos.inc
        return
  except:
    echo c
    raise
  assert false

proc tokenize*(c: var Cursor): seq[string] =
  const encodingPrefix = ["u", "u8", "U", "L"]
  const stringPrefix = ["R", "u", "u8", "U", "L"]
  while c.notAtEnd:
    assert c.cur != '\n'
    assert c.cur != '/' or c.next notin {'/', '*'}
    case c.cur:
    of Whitespace:
      c.skipPastWhitespaceAndComments()
      result &= " "
    of {'_', 'a'..'z', 'A'..'Z'}:
      result &= c.parseIdent
      if c[0] == '\'':
        doAssert result[^1] in encodingPrefix
        discard result.pop # ignore encodingPrefix
      elif c[0] == '"':
        doAssert result[^1] in stringPrefix
        doAssert result[^1] != "R"
        discard result.pop # ignore encodingPrefix
    of Digits: #TODO? floating point like .123
      if c.cur == '0' and c.next != '\0':
        if c.next == 'x' or c.next == 'X':
          c.pos += 2
          result &= c.consumeNumber(16)
          continue
        elif c.next == 'o' or c.next == 'O':
          c.pos += 2
          result &= c.consumeNumber(8)
          continue
        elif c.next in '0'..'9':
          c.pos += 1
          result &= c.consumeNumber(8)
          continue
        elif c.next == 'b' or c.next == 'B':
          c.pos += 2
          result &= c.consumeNumber(2)
          continue
        else: assert c.next != '.'
      result &= c.consumeNumber(10)
    of '{', '}', '[', ']', '(', ')', '?', ',', '~', ';':
      result &= $c.cur
      c.pos.inc
    # Not supporting alt tokens
    of '!': result &= c.consumeOperator(@["!=", "!"])
    of '#': result &= c.consumeOperator(@["##", "#"])
    of '%': result &= c.consumeOperator(@["%=", "%"]) # %> %: %:%:
    of '&': result &= c.consumeOperator(@["&&", "&=", "&"])
    of '*': result &= c.consumeOperator(@["*=", "*"])
    of '+': result &= c.consumeOperator(@["++", "+=", "+"])
    of '-': result &= c.consumeOperator(@["->*", "--", "-=", "->", "-"])
    of '/': result &= c.consumeOperator(@["/=", "/"])
    of ':': result &= c.consumeOperator(@["::", ":"]) # :>
    of '<': result &= c.consumeOperator(@["<<=", "<=>", "<=", "<<", "<"]) # <: <%
    of '>': result &= c.consumeOperator(@[">>=", ">>", ">=", ">"])
    of '=': result &= c.consumeOperator(@["==", "="])
    of '^': result &= c.consumeOperator(@["^=", "^"])
    of '|': result &= c.consumeOperator(@["|=", "||", "|"])
    of '.':
      doAssert c.next notin Digits # TODO characters
      result &= c.consumeOperator(@["...", ".*", "."])

    of '\'':
      let start = c.pos
      if c.next == '\\':
        c.pos += 3 # skip escaped char
        c.pos += c.text.skipUntil('\'', start=c.pos) + 1
      else:
        c.pos += 3
      result &= c.text[start..<c.pos]
    of '"':
      var str = "\""
      while c.more:
        c.pos.inc
        case c.cur:
        of '"': break
        of '\\':
          c.pos.inc
          if c.cur == '\\': str &= '\\'
          if c.cur == '"': str &= '"'
          else:
            echo c.next
            assert false
        else: str &= c.cur
      str &= '"'
      c.pos.inc
      result &= str
    of {'\x80'..'\xFF'}:
      doAssert false # TODO unicode?
    of {'\0'..'\x20'} - Whitespace:
      doAssert false # WTF control chars


    of '@', '`', '$', '\\', '\x7f':
      echo c
      assert false
  #for s in result.mitems: s.shallow

when isMainModule:
  var c = Cursor(text: "__GLIBC_PREREQ(2, 10)")
  echo c.tokenize
