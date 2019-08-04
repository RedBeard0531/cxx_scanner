import strformat

const header = "\"wave_wrapper.h\""

{.passL: "-lboost_wave -lboost_filesystem -lboost_system -lboost_thread".}

type
  WaveObj {.header: header, importcpp: "BoostWave" .} = object
  WaveIter {.header: header, importcpp: "BoostWave::iterator_type" .} = object
  WaveTok {.header: header, importcpp: "boost::wave::cpplexer::lex_token<>" .} = object
  WaveStr {.header: header, importcpp: "BOOST_WAVE_STRINGTYPE" .} = object
  Wave* = ref WaveObj

proc defineMacro(w: var WaveObj, m: WaveStr) {.header: header, importcpp: "add_macro_definition" .}
proc undefMacro(w: var WaveObj, m: WaveStr) {.header: header, importcpp: "remove_macro_definition" .}
proc beginIt(w: var WaveObj): WaveIter {.header: header, importcpp: "begin" .}
proc beginIt(w: var WaveObj; a, b: ptr char): WaveIter {.header: header, importcpp: "begin" .}
proc endIt(w: var WaveObj): WaveIter {.header: header, importcpp: "end" .}
proc `!=`(a, b: WaveIter): bool {.header: header, importcpp: "(# != #)" .}
proc inc(it: var WaveIter) {.header: header, importcpp: "(++#)" .}
proc `[]`(it: var WaveIter): WaveTok {.header: header, importcpp: "(*#)" .}
proc get_value(tok: WaveTok): WaveStr {.header: header, importcpp .}
converter c_str(s: WaveStr): cstring {.header: header, importcpp .}
converter `$`(s: WaveStr): string = $s.c_str
converter toWaveStr(s: cstring): WaveStr {.header: header, importcpp: "BOOST_WAVE_STRINGTYPE(@)".}

proc defineMacro*(w: Wave, m: string) =
  w[].defineMacro(m.cstring)
proc undefMacro*(w: Wave, m: string) =
  w[].undefMacro(m.cstring)

proc makeWave*(): Wave =
  var wave: ref WaveObj
  wave.new()
  {.emit: """
    new (`wave`) BoostWave(nullptr, nullptr);
    `wave`->set_language(boost::wave::support_cpp11);
  """.}
  wave.defineMacro("true=1")
  wave.defineMacro("false=0")
  wave.defineMacro("__have_feature(x)=1")
  wave.defineMacro("__has_include_next(x)=0")
  return wave

proc eval*(wave: Wave, input: string): bool =
  #echo input
  let text = &"#if ({input}) \n__X1\n#else\n__X0\n#endif"
  let endIt = wave[].endIt()
  var it = wave[].beginIt(cast[ptr char](text.cstring), cast[ptr char](cast[int](text.cstring) + text.len))
  while it != endIt:
    let res = $(it[].get_value)
    if res == "__X1": return true
    if res == "__X0": return false
    echo &"<{res}>"
    it.inc
  assert false

proc makeWave(macros: seq[string], input: string): bool =
  let wave = makeWave()
  for m in macros:
    #echo m
    wave.defineMacro(m)
  assert wave.eval(input) == wave.eval(input)
  return wave.eval(input)


proc evalCPP*(macros: seq[string], input: string): bool =
  #echo input
  return makeWave(macros, input)
