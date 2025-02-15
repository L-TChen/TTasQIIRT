-- Invariance of translation of recursor of QIIT
open import Prelude

module SC+U+Pi+Id.Translation.Recursor.Invar where

import SC+U+Pi+Id.QIIT.Syntax as I
import SC+U+Pi+Id.QIIT.Recursion as I
import SC+U+Pi+Id.QIIRT.Recursion as IR

import SC+U+Pi+Id.Translation.Syntax.Translate as ST
import SC+U+Pi+Id.Translation.Recursor.Translate as RT

module recᴵ∘>≅recᴵᴿ {ℓ ℓ′ : Level} (rec : I.Recursor {ℓ} {ℓ′}) where
  open I.Recursor rec
  open import SC+U+Pi+Id.QIIRT.Syntax
  open ST.QIIRT→QIIT
  open RT.QIIT→QIIRT
  open ≡-Reasoning

  private
    _≡,≅_ : ∀{a b}{A : Set a}{B : A → Set b}{x x' : A}{y : B x}{y' : B x'}
          → x ≡ x' → y ≅ y' → _≡_ {A = Σ A B} (x , y) (x' , y')
    p ≡,≅ q = ≅-to-≡ $ hcong₂ _,_ (≡-to-≅ p) q

  recCtxᴵ = I.recCtx rec
  recTyᴵ  = I.recTy  rec
  recSubᴵ = I.recSub rec
  recTmᴵ  = I.recTm  rec

  recCtxᴵᴿ = IR.recCtx (rec <r)
  recTyᴵᴿ  = IR.recTy  (rec <r)
  recSubᴵᴿ = IR.recSub (rec <r)
  recTmᴵᴿ  = IR.recTm  (rec <r)
  
  {-# TERMINATING #-}
  Ctxᴵᴿ≡
    : (Γ : Ctx)
    → recCtxᴵ (Γ >c) ≡ recCtxᴵᴿ Γ
  Tyᴵᴿ≅ 
    : (A : Ty Γ i)
    → recTyᴵ (A >ty) ≅ recTyᴵᴿ A
  Subᴵᴿ≅
    : (σ : Sub Γ Δ)
    → recSubᴵ (σ >s) ≅ recSubᴵᴿ σ
  Tmᴵᴿ≅
    : {A : Ty Γ i}(t : Tm Γ A)
    → recTmᴵ (t >tm) ≅ recTmᴵᴿ t
  
  Ctxᴵᴿ≡ ∅ = refl
  Ctxᴵᴿ≡ (Γ , A) = apd₂ _,ᶜᴹ_ (Ctxᴵᴿ≡ Γ) (≅-to-≡ $ HEq.trans (tr≅ (λ Γᴹ → Tyᴹ Γᴹ _) (Ctxᴵᴿ≡ Γ) (recTyᴵ (A >ty)))
                                                             (Tyᴵᴿ≅ A))
  Tyᴵᴿ≅ {Γ} (U i) = hcong (λ Γᴹ → Uᴹ {Γᴹ} i) (≡-to-≅ $ Ctxᴵᴿ≡ Γ)
  Tyᴵᴿ≅ {Γ} {i} (El t) = hcong₂ (λ Γᴹ tᴹ → Elᴹ {Γᴹ} tᴹ) (≡-to-≅ $ Ctxᴵᴿ≡ Γ) (Tmᴵᴿ≅ t)
  Tyᴵᴿ≅ {Γ} {suc i} (Lift A) = hcong₂ (λ Γᴹ Aᴹ → Liftᴹ {Γᴹ} Aᴹ) (≡-to-≅ $ Ctxᴵᴿ≡ Γ) (Tyᴵᴿ≅ A)
  Tyᴵᴿ≅ {Γ} {i} (Π A B) = icong₂ (λ Γᴹ → Tyᴹ Γᴹ i) (Ctxᴵᴿ≡ Γ) Πᴹ (Tyᴵᴿ≅ A) (Tyᴵᴿ≅ B)
  Tyᴵᴿ≅ {Γ} {i} (Id a t u) = icong₃ (λ Γᴹ → Tmᴹ Γᴹ (Uᴹ {Γᴹ} i)) (Ctxᴵᴿ≡ Γ) Idᴹ (Tmᴵᴿ≅ a) (Tmᴵᴿ≅ t) (Tmᴵᴿ≅ u)
  Subᴵᴿ≅ {Γ} ∅ = hcong (λ Γᴹ → ∅ˢᴹ {Γᴹ}) (≡-to-≅ $ Ctxᴵᴿ≡ Γ)
  Subᴵᴿ≅ {Γ} {Δ , A} (_,_ {_} {i} σ t) = icong₂ {I = Ctxᴹ × ∃ (λ Δᴹ → Tyᴹ Δᴹ i)}
                                                (λ (Γᴹ , (Δᴹ , Aᴹ)) → Subᴹ Γᴹ Δᴹ)
                                                (cong₂ _,_ (Ctxᴵᴿ≡ Γ) (Ctxᴵᴿ≡ Δ ≡,≅ Tyᴵᴿ≅ A))
                                                (λ {(Γᴹ , (Δᴹ , Aᴹ))} σᴹ tᴹ → _,ˢᴹ_ σᴹ {Aᴹ} tᴹ)
                                                (Subᴵᴿ≅ σ)
                                                (HEq.trans (icong (I.Tm (Γ >c))
                                                                  ([]>ty σ A)
                                                                   recTmᴵ
                                                                  (tr≅ (I.Tm (Γ >c)) (sym $ []>ty σ A) (t >tm)))
                                                  (HEq.trans (Tmᴵᴿ≅ t)
                                                    (HEq.sym $ tr≅ (Tmᴹ (recCtxᴵᴿ Γ)) (sym $ IR.recTy[] (rec <r) σ A) (recTmᴵᴿ t))))
  Subᴵᴿ≅ {Γ} idS = hcong (λ Γᴹ → idSᴹ {Γᴹ}) (≡-to-≅ $ Ctxᴵᴿ≡ Γ)
  Subᴵᴿ≅ {Γ} (_⨟_ {Δ} {Θ} τ σ) = icong₂ {I = Ctxᴹ × Ctxᴹ × Ctxᴹ}
                                        (λ (Γᴹ , (Δᴹ , Θᴹ)) → Subᴹ Γᴹ Δᴹ)
                                        {λ {(Γᴹ , (Δᴹ , Θᴹ))} _ → Subᴹ Δᴹ Θᴹ}
                                        (cong₂ _,_ (Ctxᴵᴿ≡ Γ) (cong₂ _,_ (Ctxᴵᴿ≡ Δ) (Ctxᴵᴿ≡ Θ)))
                                         _⨟ᴹ_
                                        (Subᴵᴿ≅ τ)
                                        (Subᴵᴿ≅ σ)
  Subᴵᴿ≅ {Γ} {Δ} (π₁ {_} {i} {A} σ) = icong {I = Ctxᴹ × ∃ (λ Δᴹ → Tyᴹ Δᴹ i)}
                                            (λ (Γᴹ , (Δᴹ , Aᴹ)) → Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ))
                                            (cong₂ _,_ (Ctxᴵᴿ≡ Γ) (Ctxᴵᴿ≡ Δ ≡,≅ Tyᴵᴿ≅ A))
                                             π₁ᴹ
                                            (Subᴵᴿ≅ σ)
  Tmᴵᴿ≅ {Γ} (π₂ {_} {Δ} {i} {A} σ) =
    HEq.trans (icong (I.Tm (Γ >c)) (sym $ []>ty (π₁ σ) A) recTmᴵ (tr≅ (I.Tm (Γ >c)) ([]>ty (π₁ σ) A) (I.π₂ (σ >s))))
              (HEq.trans (icong {I = Ctxᴹ × ∃ (λ Δᴹ → Tyᴹ Δᴹ i)}
                                (λ (Γᴹ , (Δᴹ , Aᴹ)) → Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ))
                                (cong₂ _,_ (Ctxᴵᴿ≡ Γ) (Ctxᴵᴿ≡ Δ ≡,≅ Tyᴵᴿ≅ A))
                                 π₂ᴹ
                                (Subᴵᴿ≅ σ))
                         (HEq.sym $ tr≅ (Tmᴹ (recCtxᴵᴿ Γ)) (IR.recTy[] (rec <r) (π₁ σ) A) (π₂ᴹ (recSubᴵᴿ σ))))
  Tmᴵᴿ≅ {Γ} {i} ([_]tm_ {Δ = Δ} σ {A} t) = 
    HEq.trans (icong (I.Tm (Γ >c)) (sym $ []>ty σ A) recTmᴵ (tr≅ (I.Tm (Γ >c)) ([]>ty σ A) (I.[ σ >s ]tm (t >tm))))
              (HEq.trans (icong₂ {I = Ctxᴹ × ∃ (λ Δᴹ → Tyᴹ Δᴹ i)}
                                 (λ (Γᴹ , (Δᴹ , _)) → Subᴹ Γᴹ Δᴹ)
                                 (cong₂ _,_ (Ctxᴵᴿ≡ Γ) (Ctxᴵᴿ≡ Δ ≡,≅ Tyᴵᴿ≅ A))
                                 (λ {(_ , (_ , Aᴹ))} σᴹ tᴹ → [_]tmᴹ_ σᴹ {Aᴹ} tᴹ)
                                 (Subᴵᴿ≅ σ)
                                 (Tmᴵᴿ≅ t))
                         (HEq.sym $ tr≅ (Tmᴹ (recCtxᴵᴿ Γ))
                                        (IR.recTy[] (rec <r) σ A)
                                        ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t)))
    
  Tmᴵᴿ≅ {Γ} {suc i} (c A) = icong (λ Γᴹ → Tyᴹ Γᴹ i) (Ctxᴵᴿ≡ Γ) cᴹ (Tyᴵᴿ≅ A)
  Tmᴵᴿ≅ {Γ} {suc i} (mk {A = A} t) = icong {I = ∃ (λ Γᴹ → Tyᴹ Γᴹ i)} (uncurry Tmᴹ) (Ctxᴵᴿ≡ Γ ≡,≅ Tyᴵᴿ≅ A) mkᴹ (Tmᴵᴿ≅ t)
  Tmᴵᴿ≅ {Γ} {i} (un {A = A} t) = icong {I = ∃ (λ Γᴹ → Tyᴹ Γᴹ i)}
                                       (λ (Γᴹ , Aᴹ) → Tmᴹ Γᴹ (Liftᴹ Aᴹ))
                                       (Ctxᴵᴿ≡ Γ ≡,≅ Tyᴵᴿ≅ A)
                                        unᴹ
                                       (Tmᴵᴿ≅ t)
  Tmᴵᴿ≅ {Γ} {i} (ƛ_ {A = A} {B = B} t) = icong₂ {I = ∃ (λ Γᴹ → Tyᴹ Γᴹ i)}
                                                (λ (Γᴹ , Aᴹ) → Tyᴹ (Γᴹ ,ᶜᴹ Aᴹ) i)
                                                (Ctxᴵᴿ≡ Γ ≡,≅ Tyᴵᴿ≅ A)
                                                (λ Bᴹ tᴹ → ƛᴹ_ {Bᴹ = Bᴹ} tᴹ)
                                                (Tyᴵᴿ≅ B)
                                                (Tmᴵᴿ≅ t)
  Tmᴵᴿ≅ {Γ , A} {i} (app {B = B} t) = icong₂ {I = ∃ (λ Γᴹ → Tyᴹ Γᴹ i)}
                                             (λ (Γᴹ , Aᴹ) → Tyᴹ (Γᴹ ,ᶜᴹ Aᴹ) i)
                                             (Ctxᴵᴿ≡ Γ ≡,≅ Tyᴵᴿ≅ A)
                                             (λ Bᴹ tᴹ → appᴹ {Bᴹ = Bᴹ} tᴹ)
                                             (Tyᴵᴿ≅ B)
                                             (Tmᴵᴿ≅ t)
  Tmᴵᴿ≅ {Γ} {i} (refl {a = a} t) = icong₂ (λ Γᴹ → Tmᴹ Γᴹ (Uᴹ {Γᴹ} i))
                                          (Ctxᴵᴿ≡ Γ)
                                          (λ aᴹ tᴹ → reflᴹ {aᴹ = aᴹ} tᴹ)
                                          (Tmᴵᴿ≅ a)
                                          (Tmᴵᴿ≅ t)
