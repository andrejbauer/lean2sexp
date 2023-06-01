# Convert Lean 4 `.olean` files to s-expressions

**Disclaimer:** Work in progress.

This utility converts compiled Lean 4 files to files to the [S-expression](https://en.wikipedia.org/wiki/S-expression) format.
It will convert an entire directory of `.olean` files recursively and store the result in the given output directory.
Run it like this:

```
lake exe lean2sexp 〈oleanDir〉 〈outDir〉
```

The utility is fashioned after a similar Agda backend, implemented in the
[`ast-dump` branch of this Agda fork](https://github.com/andrejbauer/agda/tree/ast-dump), see
[`src/full/Agda/Interaction/Highlighting/Sexp`](https://github.com/andrejbauer/agda/tree/ast-dump/src/full/Agda/Interaction/Highlighting/Sexp)
therein.