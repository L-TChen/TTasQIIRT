# Type theories as quotient inductive–inductive–recursive types

## Overview
This repository contains
* **manuscript** (`tex`)
* **formalisation** (`src`) – Agda implementation of type theory using both *quotient–inductive–inductive types (QIITs)* and *quotient inductive–inductive–recursive types (QIIRTs)*. 

## Contents of Formalisation
The `src` folder consists of two main parts:  

### Theory (`Theory`)  
This contains 3 variants of type theory.  
1. **Substitution Calculus** (`SC`)  
  Located in `Theory/SC`, this is the basic type theory with a single universe $\mathcal U$.  
   * Two versions: `SC/QIIT` and `SC/QIIRT`  
   * Each includes  
     * `Syntax.agda` – Syntax definition and derived properties
     * `Elimination.agda` – Elimination principle  
     * `NbE.agda` – Normalisation by evaluation of substitution calculus  
2. **Type Theory with richer universes** (`SC+U+Pi+Id`)  
  Located in `Theory/SC+U+Pi+Id`, this extends `SC` with *Coquand universe*, $\Pi$*-types*, and *extensional identity types*.  
   * Two versions: `SC+U+Pi+Id/QIIT` and `SC+U+Pi+Id/QIIRT`  
   * Each includes  
     * `Syntax.agda` – Syntax definition
     * `Properties.agda` – Derived properties
     * `Elimination.agda` – Elimination principle
     * `Recursion.agda` – Recursion principle
     * `Metacircular.agda` – Standard model definition
   * Additional in `SC+U+Pi+Id/QIIRT`  
     * `Coherence.agda` – Proof of coherence for recursive functions
3. **Boolean Extension** (`SC+U+Pi+Id+B`)  
  Located in `Theory/SC+U+Pi+Id+B`, this is an attempt of adding the *Boolean type* $\mathbf 2$ to `SC+U+Pi+Id`.  
   * Only QIIRT version is defined in `SC+U+Pi+Id+B/QIIRT/Syntax.agda`.  

### Translation (`Translation`)  
This part defines translations between QIIT and QIIRT versions of `SC+U+Pi+Id`.  
* `Translation/SC+U+Pi+Id/Syntax/Translate.agda` – Translates syntax between QIIT and QIIRT in both directions.  
* `Translation/SC+U+Pi+Id/Syntax/Iso.agda` – Proves that the syntax translation is an *isomorphism*.  
* `Translation/SC+U+Pi+Id/Recursor/Translate.agda` – Translates the recursor from QIIT to QIIRT.  


---

For clarity, here are the visualised links between the Agda formalisation and the paper.  

    src
    ├── Prelude.agda –––––––––––––––––––– Imported and predefined functions and lemmas
    ├── Theory
    │   ├── SC
    │   │   ├── QIIRT
    │   │   │   ├── Syntax.agda ––––––––– Section 3.2
    │   │   │   └── ...
    │   │   └── QIIT
    │   │       ├── Syntax.agda ––––––––– Section 3.1
    │   │       └── ...
    │   ├── SC+U+Pi+Id
    │   │   ├── QIIRT
    │   │   │   ├── Elimination
    │   │   │   │   ├── Method.agda ––––– Section 4.1
    │   │   │   │   └── Motive.agda ––––– Section 4.1
    │   │   │   ├── Elimination.agda –––– Section 4.1
    │   │   │   ├── Metacircular.agda ––– Section 4.2
    │   │   │   ├── Syntax.agda ––––––––– Section 3.3 and 3.4
    │   │   │   └── ...
    │   │   └── QIIT
    │   │       ├── Elimination
    │   │       │   ├── Method.agda ––––– Section 4.1
    │   │       │   └── Motive.agda ––––– Section 4.1
    │   │       ├── Elimination.agda –––– Section 4.1
    │   │       ├── Metacircular.agda ––– Section 4.2
    │   │       ├── Syntax.agda ––––––––– Section 3.3 and 3.4
    │   │       └── ...
    │   └── SC+U+Pi+Id+B
    │       └── QIIRT
    │           └── Syntax.agda ––––––––– Section 3.5
    └── Translation
        └── SC+U+Pi+Id
            ├── Recursor
            │   └── ...
            └── Syntax
                ├── Iso.agda –––––––––––– Section 4.3
                ├── Translate.agda –––––– Section 4.3
                └── ...




