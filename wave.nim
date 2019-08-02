import strformat

const header = "<boost/wave.hpp>"

{.passL: "-lboost_wave -lboost_filesystem -lboost_system -lboost_thread".}

{.emit: """
  #include <boost/wave.hpp>
  #include <boost/wave/cpplexer/cpp_lex_token.hpp>    // token class
  #include <boost/wave/cpplexer/cpp_lex_iterator.hpp> // lexer class
  using BoostWave = boost::wave::context<
    const char*,
    boost::wave::cpplexer::lex_iterator<boost::wave::cpplexer::lex_token<>>>;
""".}

type
  Wave {.header: header, importcpp: "BoostWave" .} = object
  WaveIter {.header: header, importcpp: "BoostWave::iterator_type" .} = object
  WaveTok {.header: header, importcpp: "boost::wave::cpplexer::lex_token<>" .} = object
  WaveStr {.header: header, importcpp: "BOOST_WAVE_STRINGTYPE" .} = object

proc makeWaveRaw(a, b: ptr char): Wave {.header: header, importcpp: "BoostWave(@)", constructor .}
proc defineMacro(w: var Wave, m: WaveStr) {.header: header, importcpp: "add_macro_definition" .}
proc beginIt(w: var Wave): WaveIter {.header: header, importcpp: "begin" .}
proc beginIt(w: var Wave; a, b: ptr char): WaveIter {.header: header, importcpp: "begin" .}
proc endIt(w: var Wave): WaveIter {.header: header, importcpp: "end" .}
proc `!=`(a, b: WaveIter): bool {.header: header, importcpp: "(# != #)" .}
proc inc(it: var WaveIter) {.header: header, importcpp: "(++#)" .}
proc `[]`(it: var WaveIter): WaveTok {.header: header, importcpp: "(*#)" .}
proc get_value(tok: WaveTok): WaveStr {.header: header, importcpp .}
converter c_str(s: WaveStr): cstring {.header: header, importcpp .}
converter `$`(s: WaveStr): string = $s.c_str
converter toWaveStr(s: cstring): WaveStr {.header: header, importcpp: "BOOST_WAVE_STRINGTYPE(@)".}

proc makeWave(macros: seq[string], input: string): seq[string] =
  var wave = makeWaveRaw(cast[ptr char](input.cstring), cast[ptr char](cast[int](input.cstring) + input.len))
  {.emit: """
    wave.set_language(boost::wave::support_cpp11);
  """.}
  for m in macros:
    #echo m
    wave.defineMacro(m.cstring)
  wave.defineMacro("true=1".cstring)
  wave.defineMacro("false=0".cstring)
  wave.defineMacro("__have_feature(x)=1".cstring)
  wave.defineMacro("__has_include_next(x)=0".cstring)
  let endIt = wave.endIt()
  var it = wave.beginIt()
  while it != endIt:
    result &= $(it[].get_value)
    #echo &"<{result[^1]}>"
    it.inc

proc evalCPP*(macros: seq[string], input: string): bool =
  #echo input
  let res = makeWave(macros, &"#if ({input}) \n__X1\n#else\n__X0\n#endif")
  #echo ""
  if res[0] == "__X1": return true
  if res[0] == "__X0": return false
  #echo res
  assert res[0] in ["__X1", "__X0"]
