open Test_funcs

let suite = [
  t "simple_float" "1.5" "" "1.5"
]

module Suite : TestSuite = struct
  let suite = suite
end