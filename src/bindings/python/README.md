[![PyPI version](https://badge.fury.io/py/yices.svg)](https://badge.fury.io/py/yices)

#  Python Bindings for Yices 2

## Installation

Once you have installed the [Yices SMT Solver](http://yices.csl.sri.com/), you can install
the python language bindings by simply installing the pip package:
```
pip install yices
```

The python API is very closely tied to the yices C API, see [yices.h](https://github.com/SRI-CSL/yices2/blob/master/src/include/yices.h).

## Examples of Usage

### The tests

The directory [test](https://github.com/SRI-CSL/yices2/tree/master/src/bindings/python/test) contains a random collection
of tests that use many of the API routines.

### The sudoku.py script

In the directory [sudoku](https://github.com/SRI-CSL/yices2/tree/master/src/bindings/python/sudoku) there is a 
yices script `sudoku.ys` and a translation `sudoku.py` that solve the same puzzle. The python version illustrates
the power of the API over the more sedate yices specification language.

### The SudokuSolver 

In the repository [SudokuSolver](https://github.com/SRI-CSL/SudokuSolver) there is a GUI that allows you to 
enter an arbitrary sudoku puzzle and solve it, and enter a partial puzzle and count the number of solutions it has.

