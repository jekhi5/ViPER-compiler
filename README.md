# The ViPER Compiler

[![Build Status](https://github.com/jekhi5/ViPER-compiler/actions/workflows/main.yaml/badge.svg?event=push)](https://github.com/jekhi5/ViPER-compiler/actions)


## Verifying Programs Execute Right

Welcome to our compiler! We've worked very hard to make your experience with our language a
positive one. ViPER is a functional language and the most current version of our language
exists in the [`src/`](src/) directory.

Thank you for using our language! We hope your programs execute right!

~ Jacob Kline and Emery Jacobowitz, Northeastern University Khoury College of Computer Science
class of '25

## Installation

## System Dependencies

Make sure that recent versions of {{:https://www.nasm.us}[nasm]} and
{{:https://clang.llvm.org}clang} are installed on your system.

ViPER primarily targets Linux. MacOS is usually supported, though platform-specific fixes may
be slower. Windows is not supported.

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

You will need to add `~/.local/bin` to your path, ideally via your shell's `rc` file (so it remains accessible between shell sessions):

```bash
echo "export PATH=$PATH:~/.local/bin" >> ~/.bashrc
source ~/.bashrc
```

You will need to add `~/.local/bin` to your path as the `viperc` install is put there.
Once complete, `viperc` will now be available on your system!

Uninstall with

```bash
make uninstall
```

### Running your own programs

To run your own programs:

1. Install the `viperc` compiler as described in [Build from Source](#build-from-source),
ensuring you add `~/.local/bin` to your path
2. Call `viperc path_to_program.viper`

View available options by running `viperc --help`

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

### Documentation

To view the documentation:

```bash
# Build the docs
make doc

# Optionally serve them locally
python scripts/server.py
```

### Adding to the testing framework

Follow the directions in the [testing README](test/input/README.md)
