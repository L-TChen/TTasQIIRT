# Formalisation of Type Theory using QII(R)T

The definition of a type theory involves a number of equations.
Here is a list of attempts we tried to strive the balence between definitional and propositional equalities.

<table>
  <thead>
    <tr>
      <td></td>
      <td colspan=2>type substitution</td>
      <td colspan=2>term substitution</td>
      <td colspan=2>term eqs</td>
      <td colspan=2>substitution eqs</td>
    </tr>
    <tr>
      <td></td>
      <td>id, comp</td>
      <td>cong</td>
      <td>id, comp</td>
      <td>wk</td>
      <td>βπ₂</td>
      <td></td>
      <td>βπ₁</td>
      <td></td>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td><details><summary>QIIT for SC</summary>
```
open import SC.QIIT
```
      </details></td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
    </tr>
    <tr>
      <td><details><summary>QIIRT for SC</summary>
```
open import SC.QIIRT
```
      </td>
      <td>🚫</td>
      <td>🔥</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🧊</td>
      <td>🚫</td>
      <td>🧊</td>
      <td>🧊</td>
    </tr>
    <tr>
      <td><details><summary>QIIRT2 for SC with El</summary>
```
open import SC.QIIRT2
```
      <td>🔥</td>
      <td>🔥</td>
      <td>🔥</td>
      <td>🧊</td>
      <td>🔥</td>
      <td>🧊</td>
      <td>🔥</td>
      <td>🧊</td>
    </tr>
  </tbody>
</table>

where

* 🧊: defined by equality constructors
* 🔥: defined by recursion possibly with rewrite rules
* 🚫: not applicable

## Trivials

* Recursion on any equality construction needs a coherence proof but does not add proof obligations to others.

* On the other hand, equality constructors can be defined without any proof obligation per se but add proof obligations to others.
