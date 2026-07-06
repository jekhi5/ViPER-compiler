# Organizing standalone test files

This directory is for handwritten, standalone test files. The subdirectories are described as follows:

- `do_err/`: Tests that should emit some error and correctly do so
- `do_pass/`: Tests that should run without errors and correctly do so
- `dont_err/`: Tests that should emit some error and incorrectly run either without errors, or emits the wrong type of error
- `dont_pass/`: Tests that should run without errors and incorrectly emits an error

Ideally, when the compiler works perfectly, the latter two directories should be empty, however these can be helpful during debugging as an organizational tool.

Tests should come in groups of related files within a single directory (from above)

- `someTest.viper`: the input program to be run
- `someTest.args`: the command line arguments to use when running the program
  - note that if this file exists, the "heap" option above is ignored
- `someTest.in`: the (optional) input to your program
- `someTest.options`: if present, options for compiling and running the program, one word per line options are
  - "valgrind" to run the program with valgrind,
  - "no_builtins" to compile the program without any predefined native functions (like `print`, `input`, or `add1`)
  - "heap" followed by an integer to run the program with the given heap size (in words)
  - "alloc" followed by either "naive" or "register" to tell the compiler which register-allocation strategy to use
- When writing tests in a `*_pass` directory, the contents of `someTest.out` will be treated as a substring to check for against the output of `someTest.viper`. If the `.out` file is missing, then the tests will simply check that the program runs without crashing
- When writing tests in a `*_err` directory, the `someTest.err` file is analogous to the `.out` file above. If the file is missing, the tests will simply check that the program either fails to compile or fails to run
