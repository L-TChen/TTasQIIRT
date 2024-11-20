# Formalisation of Type Theory using QII(R)T

The definition of a type theory involves a number of equations.
Here is a list of attempts we tried to strive the balence between definitional and propositional equalities.

<table>
  <thead>
    <tr>
      <td></td>
      <td colspan=2>type substitution</td>
      <td colspan=2>term substitution</td>
      <td>term equations (for βπ₂)</td>
      <td>term equations</td>
      <td>substitution equations</td>
    </tr>
    <tr>
      <td></td>
      <td>sub identity and composition</td>
      <td>congruence</td>
      <td>id, comp, etc</td>
      <td>weakening</td>
      <td></td>
      <td></td>
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
    </tr>
    <tr>
      <td><details><summary>QIIRT for SC</summary>
```
```
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
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
