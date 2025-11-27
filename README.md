# Type theories as quotient inductive–inductive–recursive types

## Overview
This repository contains

* **manuscript** (`tex`)
* **formalisation** (`src`) – a formalisation of type theory using *quotient inductive–inductive–recursive types (QIIRTs)*. 
## Contents of Formalisation
The `src` folder consists of two main parts:  

### Cubical library without the Glue type (`Cubical`)
This is a tiny fragment of the [cuibcal](https://github.com/agda/cubical/tree/master) library that can be checked without the `Glue` type and thus without univalence. 

### Theory (`Theory`)  
This contains three type theories as the initial natural models.

1. **Substitution Calculus** (`SC`)  
2. **Type Theory with $\Pi$-types and Booleans** (`SC+Pi+B`)  
3. **Type Theory with $\Pi$-types, Booleans, and a universe** (`SC+El+Pi+B`)  
