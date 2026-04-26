# About the archive

As detailed in the main README, the foundation of the current language exists in the form of iterative
implementations with more complex features in later versions. Our implementation culminates in our capstone project, which was
the open ended implementation of a new feature. We proposed, designed, and completed the implementation of
`try-catch` and `check-expect` style functionality. That implementation is stored for posterity in the
[viper-final-project-archive/](viper-final-project-archive/).

Feel free to check out the different iterations of the compiler. As the languages build on each other,
the final project has the most functionality of the compilers stored here.
A brief overview of what each compiler focused on is:

1. [`Adder`](adder/) (`*.adder`): Basic compiler foundation with basic arithmetic
2. [`Boa`](boa/) (`*.boa`): More binary operators and arithmetic with the addition of `let` and `if` statements
3. [`Cobra`](cobra) (`*.cobra`): Implementation of coded binary representations of values
4. [`Diamondback`](diamondback/) (`*.diamond`): Function definitions
5. [`Egg-eater`](egg-eater/) (`*.egg`): Tuples, sequencing, recursive tuples
6. [`Fer-de-lance`](fer-de-lance/) (`*.fdl`): Anonymous first-class functions
7. [`Garter`](garter/) (`*.garter`): Garbage collection
8. [`Racer`](racer/) (`*.racer`): Register allocation
9. [`Viper`](viper-final-project-archive/) (`*.viper`): `check-expect` and `try-catch`

To view the concrete syntax for each of the language iterations, check out the README in each
directory.

Additionally, there are numerous example programs in each versions' `input` folder.

## Running your own programs

To run your own programs:

1. Write program files in the given version's `input/do_pass` directory
    - The file extension must match the directory name for the language version
        - Exceptions:
          - `diamondback/`: use extension `*.diamond`
          - `egg-eater/`: use extension `*.egg`
          - `fer-de-lance/`: use extension `*.fdl`
2. Run the `COMPILER_VERSION/run` script to compile your program
3. Run the compiled `*.run` file at `output/do_pass/YOUR_PROG_NAME.run`
