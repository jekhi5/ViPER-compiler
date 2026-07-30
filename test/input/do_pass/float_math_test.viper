1
check:
  # === Addition: float + float ===
  10.05 + 11.0 spits 21.05,
  0.5 + 0.5 spits 1.0,
  3.14 + 2.86 spits 6.0,
  -5.5 + 5.5 spits 0.0,
  -3.25 + -1.75 spits -5.0,
  100.001 + 0.009 spits 100.01,

  # === Addition: float + int ===
  10.05 + 11 spits 21.05,
  0.5 + 1 spits 1.5,
  -10.5 + 5 spits -5.5,
  100.25 + -100 spits 0.25,
  0.0 + 7 spits 7.0,

  # === Addition: int + float ===
  10 + 11.6 spits 21.6,
  1 + 0.5 spits 1.5,
  5 + -10.5 spits -5.5,
  -100 + 100.25 spits 0.25,
  7 + 0.0 spits 7.0,

  # === Addition: int + int ===
  10 + 10 spits 20,
  0 + 0 spits 0,
  -5 + 5 spits 0,
  -10 + -20 spits -30,
  100 + 200 spits 300,

  # === Subtraction: float - float ===
  21.05 - 11.0 spits 10.05,
  1.0 - 0.5 spits 0.5,
  -5.5 - 5.5 spits -11.0,
  3.0 - 3.0 spits 0.0,
  -3.25 - -1.75 spits -1.5,

  # === Subtraction: float - int ===
  21.05 - 11 spits 10.05,
  1.5 - 1 spits 0.5,
  -10.5 - 5 spits -15.5,
  100.25 - -100 spits 200.25,
  7.0 - 0 spits 7.0,

  # === Subtraction: int - float ===
  21 - 11.6 spits 9.4,
  1 - 0.5 spits 0.5,
  5 - -10.5 spits 15.5,
  -100 - 100.25 spits -200.25,
  7 - 0.0 spits 7.0,

  # === Subtraction: int - int ===
  20 - 10 spits 10,
  0 - 0 spits 0,
  -5 - 5 spits -10,
  5 - -5 spits 10,
  100 - 200 spits -100,

  # === Multiplication: float * float ===
  2.0 * 2.5 spits 5.0,
  0.5 * 0.5 spits 0.25,
  -3.0 * 3.0 spits -9.0,
  -2.5 * -2.0 spits 5.0,
  10.05 * 1.0 spits 10.05,
  0.0 * 99.9 spits 0.0,

  # === Multiplication: float * int ===
  2.5 * 4 spits 10.0,
  0.5 * 3 spits 1.5,
  -3.0 * 3 spits -9.0,
  10.05 * 0 spits 0.0,
  -2.5 * -2 spits 5.0,

  # === Multiplication: int * float ===
  4 * 2.5 spits 10.0,
  3 * 0.5 spits 1.5,
  3 * -3.0 spits -9.0,
  0 * 10.05 spits 0.0,
  -2 * -2.5 spits 5.0,

  # === Multiplication: int * int ===
  10 * 10 spits 100,
  0 * 500 spits 0,
  -5 * 5 spits -25,
  -5 * -5 spits 25,
  1 * 1 spits 1
end