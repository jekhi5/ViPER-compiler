# The ViPER Compiler

## Verifying Programs Execute Right

Welcome to our compiler! We've worked very hard to make your experience with our language a positive
one. ViPER is a functional language and the most current version of our language exists in the [`src/`](src/) directory.

## Installation

### Download

Coming soon!

### Build from source

Install the source code:

```bash
git clone git@github.com:jekhi5/ViPER-compiler.git
```

The main interface is `scripts/run`, which wraps around the rules in the Makefile.

By default, `./scripts/run` will compile ViPER and build the docs. It will also run `make test` to generate a file called `tester`. Running `./tester` will run the tests. Finally, it runs `make clean`, which removes all of the build artifacts and executables.

```
Usage: run [-tcdh]

Options:
  -t    Don't run `make test`.
  -c    Don't run `make clean` after testing.
  -d    Only build the documentation.
  -h    Show this help message.
```

### Documentation

To view the documentation:

```bash
# Build the docs
./scripts/run -d # `make doc` also works

# Optionally serve them locally
python scripts/server.py
```

### Running your own programs

To run your own programs:

1. Write program files in the `test/input/do_pass` directory with the extension `*.viper`
2. Run the [`./scripts/run`](./scripts/run) script (or just `./tester` if already built) to compile your program
3. Run the compiled `.run` file at `./test/output/do_pass/YOUR_PROG_NAME.run`

Thank you for using our language! We hope your programs execute right!

~ Jacob Kline and Emery Jacobowitz, Northeastern University Khoury College of Computer Science class of '25