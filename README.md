# Type theories as quotient inductive-inductive-recursive types

## Introduction
This repository contains
* the manuscript (`tex`), and  
* the formalisation (`src`) of type theory using both quotient-inductive-inductive types (abbreviated as QIIT) and quotient inductive-inductive-recursive types (abbreviated as QIIRT) with overlapping patterns in Agda.  

In the formalisation of type theory as QIIT, we do not avoid using transport explicitly to demonstrate what is actually happening in the definitions in comparison with QIIRT.  

The key feature of the QIIRT stated here is that we use recursive functions defined by overlapping patterns in the middle of defining the type. The recursive functions are type substitution and term substitution in our formalisation of type theory as QIIRT. It can be seen that they reduced several transports that would otherwise appear in type theory as QIIT.

## Contents of Formalisation
`src` consists of two main parts, `Theory` and `Translation`.  

In `Theory`, we formalised three kinds of type theory, `SC`, `SC+U+Pi+Id`, and `SC+U+Pi+Id+B` in two possible manners, as QIIT or as QIIRT.  

1.  `Theory/SC` has the formalisation of substitution calculus with the only base universe $\mathcal U$. There are two versions of formalistion, `Theory/SC/QIIT` and `Theory/SC/QIIRT` to be compared. Each contains the syntax, elimination, and NbE of the type theory, formalised in `Syntax.agda`, `Elimination.agda`, and `NbE.agda` respectively.  

2.  `Theory/SC+U+Pi+Id` has the formalisation of substitution calculus extended with Coquand universe, $\Pi$-types, and extensional identity types.  There are also two versions of formalistion, `Theory/SC+U+Pi+Id/QIIT` and `Theory/SC+U+Pi+Id/QIIRT` to be compared. Each contains  
    * `Syntax.agda` formalising the syntax of the type theory as QIIT and QIIRT respectively,  
    * `Properties.agda` formalising the derived properties of the type theory,  
    * `Elimination.agda` formalising the elimination principle of the type theory,  
    * `Recursion.agda` formalising the recursion of the type theory, and  
    * `Metacircular.agda` formalising the standard model of the type theory.  

    `Theory/SC+U+Pi+Id/QIIRT` additionally contains
    * `Coherence.agda` formalising the proof of coherence of the recursive functions.

3. `Theory/SC+U+Pi+Id+B/QIIRT` is an attempt of adding the Boolean type $\mathbf 2$ to the type theory as QIIRT, formalised in `Syntax.agda`.  

In `Translation`, we formalised the translation between the two versions of the type theory.  
* `Translation/SC+U+Pi+Id/Syntax/Translate.agda` formalised the translation of syntax between the QIIT version and the QIIRT version of `SC+U+Pi+Id` in both direction.  
* `Translation/SC+U+Pi+Id/Syntax/Iso.agda` formalised the proof that the above syntax translation is an isomorphism.  
* `Translation/SC+U+Pi+Id/Recursor/Translate.agda` formalised the translation of recursor from the QIIT version of `SC+U+Pi+Id` to the QIIRT version of `SC+U+Pi+Id`.  

---

For clarity, here are the visualised links between the Agda formalisation and the paper.  

    src
    ├── Prelude.agda -------------------- Imported and predefined functions and lemmas
    ├── Theory
    │   ├── SC
    │   │   ├── QIIRT
    │   │   │   ├── Syntax.agda --------- Section 3.2
    │   │   │   └── ...
    │   │   └── QIIT
    │   │       ├── Syntax.agda --------- Section 3.1
    │   │       └── ...
    │   ├── SC+U+Pi+Id
    │   │   ├── QIIRT
    │   │   │   ├── Elimination
    │   │   │   │   ├── Method.agda ----- Section 4.1
    │   │   │   │   └── Motive.agda ----- Section 4.1
    │   │   │   ├── Elimination.agda ---- Section 4.1
    │   │   │   ├── Metacircular.agda --- Section 4.2
    │   │   │   ├── Syntax.agda --------- Section 3.3 and 3.4
    │   │   │   └── ...
    │   │   └── QIIT
    │   │       ├── Elimination
    │   │       │   ├── Method.agda ----- Section 4.1
    │   │       │   └── Motive.agda ----- Section 4.1
    │   │       ├── Elimination.agda ---- Section 4.1
    │   │       ├── Metacircular.agda --- Section 4.2
    │   │       ├── Syntax.agda --------- Section 3.3 and 3.4
    │   │       └── ...
    │   └── SC+U+Pi+Id+B
    │       └── QIIRT
    │           └── Syntax.agda --------- Section 3.5
    └── Translation
        └── SC+U+Pi+Id
            ├── Recursor
            │   └── ...
            └── Syntax
                ├── Iso.agda ------------ Section 4.3
                ├── Translate.agda ------ Section 4.3
                └── ...




