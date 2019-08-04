import strutils
import parseutils
import strformat

type
  Cursor* = object
    text*: string
    pos*: int

  
{.push inline.}

func `[]`*(c: Cursor, offset: int): char =
  let i = offset + c.pos
  if i < 0 or i > c.text.high: return '\0'
  return c.text[i]

func cur*(c: Cursor): char = c.text[c.pos]
func next*(c: Cursor): char = c[1]
func prev*(c: Cursor): char = c[-1]
func `$`*(c: Cursor): string = c.text & '\n' & " ".repeat(c.pos) & '^'
func more*(c: Cursor): bool = c.pos < c.text.high

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
        if cursor.text[i] == '\\':
          count.inc
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

