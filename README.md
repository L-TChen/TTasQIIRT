# Type Theories as Quotient Inductive–Inductive–Recursive Types

## Overview

This repository contains a formalisation of type theories as natural models using quotient inductive–inductive–recursive types in Cubical Agda (with the option `--cubical=no-glue`), without univalence. The development accompanies the following paper by Chen, Nordvall Forsberg, and Tsai.

#### Associated Publication

L.-T. Chen, F. Nordvall Forsberg, and T.-C. Tsai. *Can we formalise type theory intrinsically without any compromise? A case study in Cubical Agda.* In **Proceedings of the 15th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP ’26)**, New York, NY, USA, 2026. Association for Computing Machinery. doi: [10.1145/3779031.3779090](https://doi.org/10.1145/3779031.3779090).

## Requirements

* Agda 2.9.0 (development version; commit [4bcf57c](https://github.com/agda/agda/commit/4bcf57c71fbb5ce21b0fb38c00682718514ea54e) or later)

Note that at the time of writing Agda 2.9.0 is not offically released, so the option `--cubical=no-glue` is subject to change before the release.
## Contents

* **Archive** (`archive`, `archive2`): Earlier attempts using standard Agda to define type theory (for record only).
* **Manuscript** (`tex`): LaTeX sources of the accompanying paper accepted by CPP’26, based on the present formalisation (and an earlier manuscript rejected by FSCD’25 based on previous attempts).
* **Formalisation** (`src`): The main development, structured as follows.

### Cubical Library without Glue (`Cubical`)

A minimal fragment of the [cubical](https://github.com/agda/cubical/tree/master) library that typechecks without the `Glue` type and hence without univalence.

### Theory (`Theory`)

Three type theories presented as initial natural models:

1. **Substitution Calculus** (`SC`)
2. **Type Theory with $\Pi$-types and Booleans** (`SC+Pi+B`)
3. **Type Theory with $\Pi$-types, Booleans, and a universe** (`SC+El+Pi+B`)

See the [index](https://github.com/L-TChen/TTasQIIRT/blob/master/src/index.agda) for the full module list and commentary.