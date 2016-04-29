# Tiger to MIPS Compiler

Written in SML-NJ by Jiawei Zhang, Jack Gillette, and Kaighn Kevlin in Spring 2016

## Features

* Lexes and parses per Tiger Language Reference Manual in Appel's `Modern Compiler Implementation in ML`
* Typechecker fully implemented with support for built-in types (int, string), records, arrays, mutually-recursive types and function declarations, field name reusability, and variables
* Control logic:
  * `if`-`then`-`else`
  * `if`-`then`
  * `while`
  * `for`
  * `break`
* Nested `let` expressions
* Bounds checking for array accesses - no warning is provided though and program simply exits
* Standard library:
  * `print`
  * `flush`
  * `getchar`
  * `ord`
  * `chr`
  * `size`
  * `substring`
  * `concat`
  * `not`
  * `exit`

## Optimizations 

* Constant Folding
  * (int a) + (int b) = int (a+b)
  * a + 0 = a
  * 0 + b = b
  * (int a) - (int b) = int (a-b)
  * a - 0 = a
  * (int a) * (int b) = int (a*b)
  * a * 0 = 0
  * 0 * b = 0
  * a * 1 = a
  * 1 * b = b
  * (int a) / (int b) = int (a/b)
  * 0 / b = 0
  * a / 1 = a
* $0 used for constant 0
* Binop for memory is optimized to use offset `N` (`lw $t0, N($t1)`)

## How to Run

```
CM.make "sources.cm";
Main.compile "file.tig";
```

This outputs `file.tig.s` and `log.txt`.

`file.tig.s` can be run in SPIM (legacy-spim or QT-SPIM) without modifications. The `in`-`end` value of the outermost `let` has its value stored in `$v1` at the end of execution. 

The compiled code begins around line 760. The rest are runtime library fragments.

`log.txt` contains debug information, including IR, original assembly instructions, and final assembly instructions

## Sample Programs

* queens.tig - solves the 8-queens problem and displays solutions with an 8x8 character grid (92 of them)
* merge.tig - performs merge-sort on two lists of integers
  * ints are separated by spaces
  * lists are separated by semicolon