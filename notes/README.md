# Mathematical note

[PDF](monodromy-note.pdf) · [LaTeX](monodromy-note.tex) · [Review package](monodromy-review.zip)

The draft dated 4 November 2026 develops conditional winding, the shared
three-root covering, native operations, finite execution, and Theorem 5.1
on geometric Turing universality. It has six main pages and a one-page
proof index, with Computer Modern typography and two vector figures.

## Review package

The ZIP opens directly to one complete project:

```text
Monodromy/
  Monodromy.pdf
  README.md
  lakefile.lean
  lean-toolchain
  lake-manifest.json
  src/Monodromy.lean
  src/Audit.lean
  src/Monodromy/*.lean
```

Its single README contains the proof index, exact source version, build
instructions, attribution, and the existing software notice. The 18 Lean
sources and three build files preserve the reviewed proof tree byte for
byte. Their reproducible source-tree SHA-256 is
`5cace91af9a10ffd4498248e56d1260892a09d2d01f8d1fcb24c1703f5b34539`;
the package README specifies the calculation.

From the extracted `Monodromy/` directory, run:

```sh
lake exe cache get
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

The actual ZIP was checked in a new directory on macOS 15.4.1 (arm64),
with Lean 4.35.0 and a fresh project build. The nine external dependency
checkouts and their build caches were shared through `.lake/packages`;
all revisions matched the lockfile. The three commands passed: 3071 Lake
jobs and a strict audit of 1531 Monodromy declarations using only the
standard Lean axioms. Every page of the final PDF was rendered and inspected.

The numbered Lean companions in this directory remain navigation copies
of the same frozen sources. Active research in `src/Monodromy/` advances
independently; the review package fixes the proof version used by this note.

To compile the standalone manuscript from this repository's root:

```sh
cd notes
latexmk -pdf monodromy-note.tex
```
