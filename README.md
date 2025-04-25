# The ViPER Compiler
## Verifying Programs Execute Right

Welcome to our compiler! We've worked very hard to make your experience with our langauge a positive
one. ViPER is a functional langauge and each of the directories above holds a progressively more 
developed compiler. Our implementation culminates in our capstone project, which was the open ended 
implementation of a new feature. We proposed, designed, and completed the implementation of 
`try-catch` and `check-expect` style functionality.

Feel free to check out the different iterations of the compiler, each assignment building off all of 
the previous ones. As the assignments build on eachother, the final project has the most functionality. 
A brief overview of what each assignment focused on, starting in Assignment 2 is:

2. `Adder` (`*.adder`): Basic compiler foundation with basic arithmetic
3. `Boa` (`*.boa`): More binary operators and arithmetic with the addition of `let` and `if` statements
4. `Cobra` (`*.cobra`): Implementation of coded binary representations of values
5. `Diamondback` (`*.diamond`): Function definitions
6. `Egg-eater` (`*.egg`): Tuples, sequencing, recursive tuples
8. `Fer-de-lance` (`*.fdl`): Anonymous first-class functions
9. `Garter` (`*.garter`): Garbage collection
10. `Racer` (`*.racer`): Register allocation
11. `Final` (`*.viper`): `check-expect` and `try-catch`

To view the concrete syntax for each of the langauge iterations, check out the README in each
directory. To learn more about our final project, check out the README in that directory.
Additionally, there are numerous example programs in each assignment's `input` folder.

### Running your own programs:

To run your own programs:
1. Write program files in the input directory under `do_pass` in the desired assignment directory
    - The file extension should match the corresponding file extension for that directory listed above
3. Run the `run` script in that assignment's root directory to compile your program
4. Run the compiled `*.run` file at `output/do_pass/YOUR_PROG_NAME.run`

Thank you for using our language! We hope your programs execute right!

\- Jacob Kline and Emery Jacobowitz, Northeastern University Khoury College of Computer Science class of '25