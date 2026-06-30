# The ViPER Compiler

## Verifying Programs Execute Right

Welcome to our compiler! We've worked very hard to make your experience with our language a positive
one. ViPER is a functional language and the most current version of our language exists in the [`src/`](src/) directory.

## Installation

## System Dependencies

Make sure that recent versions of {{:https://www.nasm.us}[nasm]} and {{:https://clang.llvm.org}clang} are installed on your system.

Currently, ViPER primarily targets Linux. MacOS is occassionally supported. Windows is not supported. 

### Download

Coming soon!

### Build from source

Install the source code and dependencies:

```bash
git clone git@github.com:jekhi5/ViPER-compiler.git
cd ViPER-compiler
opam install .
```
To build ViPER, run

```bash
make && make install
```

Now the ViPER compiler, `viperc`, will be available on your system. 

Uninstall with

```bash
make uninstall
```

### Development

The main interface is the Makefile. Here is a general workflow:

```bash
> make clean                    # Remove development artifacts
> make                          # Build the project
> make test                     # Build the tester
> ./tester                      # Run the tests
> bisect-ppx-report html        # Generate a detailed test coverage report
> python scripts/server.py -c   # View the test coverage report at localhost:8080
```

### Test Coverage

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