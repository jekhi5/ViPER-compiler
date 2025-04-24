# The ViPER Compiler
## Verifying Programs Execute Right

Welcome to our compiler! We've worked very hard to make your experience with our langauge a positive
one. ViPER is a functional langauge and in each of the directories above, the compiler has more and 
more functionality, culminating in our capstone project which was the open ended implementation of a 
new feature. We proposed and ultimately chose the implementation of `try-catch` and `check-expect` 
style functionality.

Feel free to check out the different iterations of the compiler, each assignment building off all of 
the previous ones. The final project is based on all of the functionality, so it's inherently has the 
most functionality. A brief overview of what each assignment focused on, starting in Assignment 3 is:

2. Adder: Basic compiler foundation with basic arithmetic
3. Boa: More binary operators and arithmetic with the addition of `let` and `if` statements
4. Cobra: Implementation of coded binary representations of values
5. Diamondback: Function definitions
6. Egg-eater: Tuples, sequencing, recursive tuples
8. Fer-de-lance: Anonymous first-class functions
9. Garter: Garbace collection
10. Racer: Register allocation
11. Final: `check-expect` and `try-catch`

To view the concrete syntax for each of the langauge iterations, check out the README in each
directory. To learn more about our final project, check out the README in that directory.
Additionally, there are numerous example programs in each assignment's `input` folder.

### Running your own programs:

To run your own programs:
1. Write them in the input directory under `do_pass` in the assignment directory you want. 
2. Run the `run` script in that assignment's root dir 
3. Run the compiled `*.run` file at `output/do_pass/YOUR_PROG_NAME.run`

Thank you for using our language! We hope your programs execute right!

\- Jacob Kline and Emery Jacobowitz, Northeastern University Khoury College of Computer Science class of '25