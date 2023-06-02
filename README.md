# Convert Lean 4 `.olean` files to s-expressions

This utility converts compiled Lean 4 files to files to the [S-expression](https://en.wikipedia.org/wiki/S-expression) format. These can be used for further processing, e.g., for machine-learning purposes.

## Installation

In order to use `lean2sexp` in a Lean project, add the following line to `lakefile.lean`:

```
require lean2sexp from git
  "https://github.com/andrejbauer/lean2sexp.git" @ "main"
```

## Usage

By default, `lean2sexp` converts all files found in the project subdirectory `build/lib` and stores them in the folder `sexp`. (This means you should build the project before running `lean2sexp`, and possibly remove `sexp` folder to get rid of stale files.)

To generate the files with s-expressions, run

```
lake exe lean2sexp
```

Optionally, you may provide the input and output folders (or just the input folder):

```
lake exe lean2sexp 〈oleanDir〉 〈sexpDir〉
```

## Background

The utility is fashioned after a similar Agda backend, implemented in the
[`ast-dump` branch of this Agda fork](https://github.com/andrejbauer/agda/tree/ast-dump), see
[`src/full/Agda/Interaction/Highlighting/Sexp`](https://github.com/andrejbauer/agda/tree/ast-dump/src/full/Agda/Interaction/Highlighting/Sexp)
therein.
