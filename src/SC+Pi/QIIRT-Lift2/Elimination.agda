-- Elimination of Substitution Calculus
module SC+Pi.QIIRT-Lift2.Elimination where

open import Prelude
  hiding (_,_)
open import SC+Pi.QIIRT-Lift2.Base
open import SC+Pi.QIIRT-Lift2.Cong
open import SC+Pi.QIIRT-Lift2.Model

module elim {i j}(P : Pdc {i} {j})(indCL : IH-Ctx-Lift P)(indP : IH P indCL) where
  open Pdc P
  open IH-Ctx-Lift indCL
  open IH indP

  {-# TERMINATING #-}
  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimLift : (Ξ : Lift Γ) → PLift (ElimCtx Γ) Ξ
  Elim++ : (Γ : Ctx)(Ξ : Lift Γ) → ElimCtx (Γ ++ Ξ) ≡ ElimCtx Γ ++P ElimLift Ξ
  ElimTy : (A : Ty Γ) → PTy (ElimCtx Γ) A
  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t
  ElimTy[] : (σ : Sub Δ Γ)(A : Ty Γ) → conv (PTy` refl (sym (trans (cong (ElimCtx Δ ++P_) (∅[]lP _)) (++P∅ _))) refl) (ElimTy ([ σ ] A))
                                     ≡ [ ∅Lift ⇈ ElimSub σ ]P conv (PTy` refl (sym (++P∅ (ElimCtx Γ))) refl)
                                                                   (ElimTy A)

  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  ElimLift ∅ = ∅Lift
  ElimLift {Γ} (Ξ , A) = ElimLift Ξ ,Lift conv (PTy` refl (Elim++ Γ Ξ) refl) (ElimTy A)
  Elim++ Γ ∅ = sym (++P∅ (ElimCtx Γ))
  Elim++ Γ (Ξ , A) = sym eq
    where
      open ≡-Reasoning
      eq : ElimCtx Γ ++P (ElimLift Ξ ,Lift conv (PTy` refl (Elim++ Γ Ξ) refl) (ElimTy A))
         ≡ ElimCtx (Γ ++ Ξ) ,Ctx ElimTy A
      eq = begin
          ElimCtx Γ ++P (ElimLift Ξ ,Lift conv (PTy` refl (Elim++ Γ Ξ) refl) (ElimTy A))
        ≡⟨ ++P, (ElimCtx Γ) (ElimLift Ξ)
                (conv (PTy` refl (Elim++ Γ Ξ) refl) (ElimTy A)) ⟩
          (ElimCtx Γ ++P ElimLift Ξ) ,Ctx conv (PTy` refl (Elim++ Γ Ξ) refl) (ElimTy A)
        ≡⟨ sym (,Ctx` (Elim++ Γ Ξ) refl) ⟩
          ElimCtx (Γ ++ Ξ) ,Ctx ElimTy A
        ∎
  ElimTy U = PU
  ElimTy (Π A B) = PΠ (ElimTy A) (ElimTy B)
  ElimTy[] {Δ} {Γ} σ U = ≅-to-≡ $ begin
      conv (PTy` refl (sym (trans (cong (ElimCtx Δ ++P_) (∅[]lP _)) (++P∅ _))) refl) PU
    ≅⟨ conv-rm (PTy` refl (sym (trans (cong (ElimCtx Δ ++P_) (∅[]lP _)) (++P∅ _))) refl) _ ⟩
      PU {PΓ = ElimCtx Δ}
    ≅⟨ HEq.cong (λ p → PU {PΓ = p}) (≡-to-≅ (sym eq)) ⟩
      PU {PΓ = ElimCtx Δ ++P ([ ElimSub σ ]lP ∅Lift)}
    ≅⟨ HEq.sym (≡-to-≅ (PU[] ∅Lift (ElimSub σ))) ⟩
      [ ∅Lift ⇈ ElimSub σ ]P PU
    ≡⟨ cong (λ p → [ ∅Lift ⇈ ElimSub σ ]P p) (sym eq') ⟩
      [ ∅Lift ⇈ ElimSub σ ]P conv (PTy` refl (sym (++P∅ (ElimCtx Γ))) refl) PU
    ∎
    where
      open ≅-Reasoning
      eq : ElimCtx Δ ++P ([ ElimSub σ ]lP ∅Lift) ≡ ElimCtx Δ
      eq = trans (cong (ElimCtx Δ ++P_) (∅[]lP _)) (++P∅ _)
      eq' : conv (PTy` refl (sym (++P∅ (ElimCtx Γ))) refl) PU ≡ PU
      eq' = ≅-to-≡ $ begin
          conv (PTy` refl (sym (++P∅ (ElimCtx Γ))) refl) PU
        ≅⟨ conv-rm (PTy` refl (sym (++P∅ (ElimCtx Γ))) refl) _ ⟩
          PU {PΓ = ElimCtx Γ}
        ≅⟨ HEq.cong (λ p → PU {PΓ = p}) (≡-to-≅ (sym (++P∅ _))) ⟩
          PU {PΓ = ElimCtx Γ ++P ∅Lift}
        ∎
  ElimTy[] {Δ} {Γ} σ (Π A B) = ≅-to-≡ $ begin
      conv (PTy` refl (sym (trans (cong (ElimCtx Δ ++P_) (∅[]lP _)) (++P∅ _))) refl)
           (PΠ (ElimTy ([ ∅ ⇈ σ ] A)) (ElimTy ([ ∅ , A ⇈ σ ] B)))
    ≅⟨ conv-rm (PTy` refl (sym (trans (cong (ElimCtx Δ ++P_) (∅[]lP _)) (++P∅ _))) refl) _ ⟩
      PΠ (ElimTy ([ ∅ ⇈ σ ] A)) (ElimTy ([ ∅ , A ⇈ σ ] B))
    ≅⟨ {! ElimTy ([ ∅ , A ⇈ σ ] B)  !} ⟩
      {!  PΠ[]  !}
    where
      open ≅-Reasoning
  ElimSub ∅ = ∅Sub
  ElimSub idS = PidS
  ElimSub (σ ⨟ τ) = ElimSub σ ⨟P ElimSub τ
  ElimSub {Δ} {Γ , A} (σ , t) = conv (sym (PSubPΓ` {PΓ = ElimCtx Δ}
                                                   {ElimCtx Γ ,Ctx ElimTy A}
                                                   {ElimCtx Γ ,Ctx conv (PTy` refl (++P∅ (ElimCtx Γ)) refl) _}
                                                    refl
                                                   (sym eq1)
                                                    refl))
                                     (ElimSub σ ,Sub conv (PTm` refl (sym eq2) refl eq3 refl) (ElimTm t))
    where
      eq1 : ElimCtx Γ ,Ctx conv (PTy` refl (++P∅ (ElimCtx Γ)) refl) (conv (PTy` refl (Elim++ Γ ∅) refl) (ElimTy A))
          ≡ ElimCtx Γ ,Ctx ElimTy A
      eq1 = begin
          ElimCtx Γ ,Ctx conv (PTy` refl (++P∅ (ElimCtx Γ)) refl) (conv (PTy` refl (Elim++ Γ ∅) refl) (ElimTy A))
        ≡⟨ cong (ElimCtx Γ ,Ctx_) (conv² (PTy` refl (Elim++ Γ ∅) refl) (PTy` refl (++P∅ (ElimCtx Γ)) refl)) ⟩
          ElimCtx Γ ,Ctx conv _ (ElimTy A)
        ≡⟨ cong (ElimCtx Γ ,Ctx_) (conv-unique _ refl (ElimTy A)) ⟩
          ElimCtx Γ ,Ctx ElimTy A
        ∎
        where open ≡-Reasoning
      eq2 : ElimCtx Δ ++P ([ ElimSub σ ]lP ∅Lift) ≡ ElimCtx Δ
      eq2 = trans (cong (ElimCtx Δ ++P_) (∅[]lP (ElimSub σ))) (++P∅ (ElimCtx Δ))
      eq3 : conv (PTy` refl (sym eq2) refl) (ElimTy ([ σ ] A))
          ≡ [ ∅Lift ⇈ ElimSub σ ]P conv (PTy` refl (Elim++ Γ ∅) refl) (ElimTy A)
      eq3 = ElimTy[] σ A
  ElimSub (π₁ σ) = {!   !}
  ElimTm t = {!   !}

  -- {-# TERMINATING #-}
  -- ElimTy[] : (A : Ty Γ)(σ : Sub Δ Γ) → ElimTy A [ ElimSub σ ]P ≡ ElimTy (A [ σ ])
  -- ElimTm[] : (t : Tm Γ A)(σ : Sub Δ Γ)
  --          → conv (PTmPΓ` refl (ElimTy[] A σ) refl) (ElimTm t [ ElimSub σ ]tP) ≡ ElimTm (t [ σ ]t)

  -- ElimCtx ∅ = ∅Ctx
  -- ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  -- ElimTy U = PU
  -- ElimTy (El u) = PEl (ElimTm u)
  -- ElimTy[] U σ = PU[]
  -- ElimTy[] {Γ} {Δ} (El u) σ = begin
  --     (ElimTy (El u) [ ElimSub σ ]P)
  --   ≡⟨ PEl[] {Pu = ElimTm u} (ElimSub σ) ⟩
  --     PEl (conv (PTmPΓ` refl PU[] refl) (ElimTm u [ ElimSub σ ]tP))
  --   ≡⟨ cong PEl (ElimTm[] u σ) ⟩
  --     PEl (ElimTm (u [ σ ]t))
  --   ∎
  --   where open ≡-Reasoning
  -- ElimSub ∅ = ∅Sub
  -- ElimSub {Δ} (_,_ {A = A} σ t) = ElimSub σ ,Sub conv (PTmPΓ` refl (sym (ElimTy[] A σ)) refl)
  --                                                     (ElimTm t)
  -- ElimSub idS = PidS
  -- ElimSub (σ ∘ τ) = ElimSub σ ∘P ElimSub τ
  -- ElimSub (π₁ σ) = π₁P (ElimSub σ)
  -- ElimTm {Γ} (π₂ {A = A} σ) = conv (PTmPΓ` refl (ElimTy[] A (π₁ σ)) refl) (π₂P (ElimSub σ))
  -- ElimTm {Γ} (_[_]tm {A = A} t σ) = conv (PTmPΓ` refl (ElimTy[] A σ) refl) (ElimTm t [ ElimSub σ ]tmP)
  -- ElimTm[] (π₂ {A = A} σ) τ = ≅-to-≡ $ begin
  --     conv (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) (ElimTm (π₂ σ) [ ElimSub τ ]tP)
  --   ≅⟨ conv-rm (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) _ ⟩
  --     ElimTm (π₂ σ) [ ElimSub τ ]tP
  --   ≅⟨ ≡-to-≅ (sym ([]tmP≡[]tP (ElimTm (π₂ σ)) (ElimSub τ))) ⟩
  --     conv (PTmPΓ` refl refl ([]tm≡[]t (π₂ σ) τ)) (ElimTm (π₂ σ) [ ElimSub τ ]tmP)
  --   ≅⟨ conv~unique (PTmPΓ` refl refl ([]tm≡[]t (π₂ σ) τ)) (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) _ ⟩
  --     conv (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) (ElimTm (π₂ σ) [ ElimSub τ ]tmP)
  --   ≅⟨ refl ⟩
  --     ElimTm (π₂ σ [ τ ]tm)
  --   ≅⟨ HEq.cong ElimTm (≡-to-≅ ([]tm≡[]t (π₂ σ) τ)) ⟩
  --     ElimTm (π₂ σ [ τ ]t)
  --   ∎
  --   where open ≅-Reasoning 
  -- ElimTm[] (_[_]tm {A = A} t σ) τ = ≅-to-≡ $ begin
  --     conv (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) (ElimTm (t [ σ ]tm) [ ElimSub τ ]tP)
  --   ≅⟨ conv-rm (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) _ ⟩
  --     ElimTm (t [ σ ]tm) [ ElimSub τ ]tP
  --   ≅⟨ ≡-to-≅ (sym ([]tmP≡[]tP (ElimTm (t [ σ ]tm)) (ElimSub τ))) ⟩
  --     conv (PTmPΓ` refl refl ([]tm≡[]t (t [ σ ]tm) τ)) (ElimTm (t [ σ ]tm) [ ElimSub τ ]tmP)
  --   ≅⟨ conv~unique (PTmPΓ` refl refl ([]tm≡[]t (t [ σ ]tm) τ)) (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) _ ⟩
  --     conv (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) (ElimTm (t [ σ ]tm) [ ElimSub τ ]tmP)
  --   ≅⟨ refl ⟩
  --     ElimTm (t [ σ ]tm [ τ ]tm)
  --   ≅⟨ HEq.cong ElimTm (≡-to-≅ ([]tm≡[]t (t [ σ ]tm) τ)) ⟩
  --     ElimTm (t [ σ ]tm [ τ ]t)
  --   ∎    
  --   where open ≅-Reasoning 