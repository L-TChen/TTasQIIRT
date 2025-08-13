TOOD by 29 Aug

* Finish variants of NbE for SC / (SC+El+Pi+B, if we have enough time) 
  - SC/QIIRT-tyOf/IxModels/[NbE.agda, StrictNbE.agda, NbEwithIsoReasoning.agda]
  - [optional] SC+El+Pi+B

* Finish SC+El+Pi+B with logical predicate interpretation
  * Finish elimination (IxModel is done)
  - SC+El+Pi+B/QIIRT-tyOf/Elim.agda (not yet)
  - SC+El+Pi+B/QIIRT-tyOf/IxModels/LogPred.agda (not yet)
  - SC/QIIRT-tyOf/IxModels/LogPred.agda (half done)

* Finish the canonicity proof for SC+Pi+B (with just Yoneda embedding) 
  - SC+Pi+B/QIIRT-tyOf/DisplayedModel.agda (not yet)
  - SC+Pi+B/QIIRT-tyOf/Elim.agda (not yet)
  - SC+Pi+B/QIIRT-tyOf/Canoncity.agda

* Adapt the strictification by Kaposi & Pujet (2025)

* Finish the canonicity proof for SC+Pi+B (with strictification) 
  - SC+Pi+B/QIIRT-tyOf/Canoncity.agda

Motivation for the paper:

- Start with the NbE using strict syntax and explain it does not seem practical to use.
