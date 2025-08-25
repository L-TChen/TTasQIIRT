{-# OPTIONS --hidden-argument-puns #-}

open import Prelude

open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.DisplayedModel (M : SC ℓ₁' ℓ₂' ℓ₃' ℓ₄') where

private
  module S = SC M

open S hiding (module Var)
open S.Var hiding (C)

record Motive∙ (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctx∙
      : (Γ : Ctx)
      → Set ℓ₁
    Ty∙
      : Ctx∙ Γ → Ty Γ
      → Set ℓ₂
    Sub∙
      : (Γ∙ : Ctx∙ Γ) (Δ∙ : Ctx∙ Δ) → Sub Γ Δ
      → Set ℓ₃
    Tm∙
      : Ctx∙ Γ → Tm Γ
      → Set ℓ₄
    tyOf∙
      : {Γ∙ : Ctx∙ Γ} → Tm∙ Γ∙ t
      → Ty∙ Γ∙ (tyOf t)

--   -- SC∙ is defined separately from Motive in order to declare
--   -- generalizable variables.

  infix 4 _≡Ty[_]_ _≡Tm[_]_ _≡Sub[_]_

  _≡Ty[_]_
    : {Γ∙ : Ctx∙ Γ}
    → Ty∙ Γ∙ A → A ≡ B → Ty∙ Γ∙ B → Type ℓ₂
  _≡Ty[_]_ {Γ∙} A∙ e B∙ = PathP (λ i → Ty∙ Γ∙ (e i)) A∙ B∙
  {-# INJECTIVE_FOR_INFERENCE _≡Ty[_]_ #-}

  _≡Sub[_]_
    : {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ}
    → Sub∙ Γ∙ Δ∙ σ → σ ≡ τ → Sub∙ Γ∙ Δ∙ τ → Type ℓ₃
  _≡Sub[_]_ {Γ∙} {Δ∙} σ∙ e τ∙ = PathP (λ i → Sub∙ Γ∙ Δ∙ (e i)) σ∙ τ∙
  {-# INJECTIVE_FOR_INFERENCE _≡Sub[_]_ #-}

  _≡Tm[_]_
    : {Γ∙ : Ctx∙ Γ}
    → Tm∙ Γ∙ t → t ≡ u → Tm∙ Γ∙ u → Type ℓ₄
  _≡Tm[_]_ {Γ∙} t∙ e u∙ = PathP (λ i → Tm∙ Γ∙ (e i)) t∙ u∙
  {-# INJECTIVE_FOR_INFERENCE _≡Tm[_]_ #-}

  module Var where
    variable
      Γ∙ Δ∙ Θ∙ Ξ∙ : Ctx∙ Γ
      A∙ B∙ C∙ D∙ : Ty∙  Γ∙ A
      σ∙ τ∙ γ∙    : Sub∙ Γ∙ Δ∙ σ
      t∙ u∙ v∙    : Tm∙  Γ∙ t
  open Var

module _ (mot : Motive∙ ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motive∙ mot
  open Var hiding (C∙)

  open S
  open S.Var

  record IsSC∙ : Set (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      ∅∙
        : Ctx∙ ∅
      _,∙_
        : (Γ∙ : Ctx∙ Γ)(A∙ : Ty∙ Γ∙ A)
        → Ctx∙ (Γ ,C A)
      _[_]T∙
        : (A∙ : Ty∙ Δ∙ A)(σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → Ty∙ Γ∙ (A [ σ ]T)
      _[_]t∙
        : (t∙ : Tm∙ Δ∙ t)(σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → Tm∙ Γ∙ (t [ σ ]t)
      tyOf[]∙
        : {t∙ : Tm∙ Δ∙ t} {σ∙ : Sub∙ Γ∙ Δ∙ σ}
        → tyOf∙ (t∙ [ σ∙ ]t∙)
        ≡Ty[ tyOf[] ] (tyOf∙ t∙ [ σ∙ ]T∙)

      ∅S∙
        : Sub∙ Γ∙ ∅∙ ∅S
      _,_∶[_,_]∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) {A∙ : Ty∙ Δ∙ A} (t∙ : Tm∙ Γ∙ t)
        → (p : tyOf t ≡ A [ σ ]T)
        → tyOf∙ t∙ ≡Ty[ p ] (A∙ [ σ∙ ]T∙)
        → Sub∙ Γ∙ (Δ∙ ,∙ A∙) (σ , t ∶[ p ])
      idS∙
        : Sub∙ Γ∙ Γ∙ idS
      _∘∙_
        : Sub∙ Δ∙ Θ∙ τ → Sub∙ Γ∙ Δ∙ σ
        → Sub∙ Γ∙ Θ∙ (τ ∘ σ)
      π₁∙
        : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ
        → Sub∙ Γ∙ Δ∙ (π₁ σ)
      π₂∙
        : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ
        → Tm∙ Γ∙ (π₂ σ)
      tyOfπ₂∙
        : (σ∙ : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ)
        → tyOf∙ (π₂∙ σ∙) ≡Ty[ tyOfπ₂ σ ] A∙ [ π₁∙ σ∙ ]T∙
      idS∘∙_
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → idS∙ ∘∙ σ∙
          ≡Sub[ idS∘ σ ] σ∙
      _∘idS∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → σ∙ ∘∙ idS∙
          ≡Sub[ σ ∘idS ] σ∙
      assocS∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (τ∙ : Sub∙ Δ∙ Θ∙ τ) (γ∙ : Sub∙ Θ∙ Ξ∙ γ)
        → (γ∙ ∘∙ τ∙) ∘∙ σ∙
        ≡Sub[ assocS σ τ γ ]
          γ∙ ∘∙ (τ∙ ∘∙ σ∙)
      ,∘∙
        : (σ∙ : Sub∙ Δ∙ Θ∙ σ) (t∙ : Tm∙ Δ∙ t) (τ∙ : Sub∙ Γ∙ Δ∙ τ)
          (p : tyOf t ≡ A [ σ ]T) (p∙ : tyOf∙ t∙ ≡Ty[ p ] A∙ [ σ∙ ]T∙)
          (q : tyOf (t [ τ ]t) ≡ A [ σ ∘ τ ]T) (q∙ : tyOf∙ (t∙ [ τ∙ ]t∙) ≡Ty[ q ] (A∙ [ σ∙ ∘∙ τ∙ ]T∙))
        → (σ∙ , t∙ ∶[ p , p∙ ]∙) ∘∙ τ∙
          ≡Sub[ ,∘ σ t τ p q ]
          (σ∙ ∘∙ τ∙) , t∙ [ τ∙ ]t∙ ∶[ q , q∙ ]∙
      ηπ∙
        : (σ∙ : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ)
        → σ∙
          ≡Sub[ ηπ σ ]
          (π₁∙ σ∙ , π₂∙ σ∙ ∶[ tyOfπ₂ σ , tyOfπ₂∙ σ∙ ]∙)
      η∅∙
        : (σ∙ : Sub∙ Γ∙ ∅∙ σ)
        → σ∙ ≡Sub[ η∅ σ ] ∅S∙
      βπ₁∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (t∙ : Tm∙ Γ∙ t)
        → (p : tyOf t ≡ A [ σ ]T) (p∙ : tyOf∙ t∙ ≡Ty[ p ] A∙ [ σ∙ ]T∙)
        → π₁∙ (σ∙ , t∙ ∶[ p , p∙ ]∙) ≡Sub[ βπ₁ σ t p ] σ∙
      βπ₂∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (t∙ : Tm∙ Γ∙ t)
        → (p : tyOf t ≡ A [ σ ]T) (p∙ : tyOf∙ t∙ ≡Ty[ p ] A∙ [ σ∙ ]T∙)
        → (q : A [ π₁ (σ , t ∶[ p ]) ]T ≡ tyOf t)
          (q∙ : A∙ [ π₁∙ (σ∙ , t∙ ∶[ p , p∙ ]∙) ]T∙ ≡Ty[ q ] tyOf∙ t∙)
        → π₂∙ (σ∙ , t∙ ∶[ p , p∙ ]∙)
        ≡Tm[ βπ₂ σ t p ]
          t∙
      [idS]T∙
        : (A∙ : Ty∙ Γ∙ A)
        → A∙ ≡Ty[ [idS]T {Γ} {A} ] (A∙ [ idS∙ ]T∙)
      [∘]T∙
        : (A∙ : Ty∙ Θ∙ A) (σ∙ : Sub∙ Γ∙ Δ∙ σ) (τ∙ : Sub∙ Δ∙ Θ∙ τ)
        → A∙ [ τ∙ ]T∙ [ σ∙ ]T∙
        ≡Ty[ [∘]T A σ τ ]
          A∙ [ τ∙ ∘∙ σ∙ ]T∙
      [idS]t∙
        : (t∙ : Tm∙ Γ∙ t)
        → t∙
        ≡Tm[ [idS]t t ]
          t∙ [ idS∙ ]t∙
      [∘]t∙
        : (t∙ : Tm∙ Θ∙ t) (σ∙ : Sub∙ Γ∙ Δ∙ σ) (τ∙ : Sub∙ Δ∙ Θ∙ τ)
        → t∙ [ τ∙ ]t∙ [ σ∙ ]t∙
        ≡Tm[ [∘]t t σ τ ]
          t∙ [ τ∙ ∘∙ σ∙ ]t∙
      U∙
        : Ty∙ Γ∙ A
      U[]∙
        : {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {σ∙ : Sub∙ Γ∙ Δ∙ σ}
        → U∙ [ σ∙ ]T∙
        ≡Ty[ U[] {σ = σ} ]
          U∙

record SC∙ (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    C∙    : Motive∙ ℓ₁ ℓ₂ ℓ₃ ℓ₄
    isSC∙ : IsSC∙ C∙

  open Motive∙ C∙  public
  open IsSC∙ isSC∙ public

  -- adapted from 1Lab
  infixr 30 _∙Ty[]_ ∙Ty[-]-syntax ∙Sub[-]-syntax _∙Sub[]_ _∙Tm[]_ ∙Tm[-]-syntax 
  infixr 2 ≡Ty[]⟨⟩-syntax ≡Ty[-]⟨⟩-syntax ≡Sub[]⟨⟩-syntax ≡Sub[-]⟨⟩-syntax ≡Tm[]⟨⟩-syntax ≡Tm[-]⟨⟩-syntax 
  infix 1 beginTy_ beginTy[_]_ beginSub_ beginSub[_]_ beginTm_ beginTm[_]_

  open Var

  _∙Ty[]_
    : {A B C : Ty Γ} {Γ∙ : Ctx∙ Γ} 
    → {A∙ : Ty∙ Γ∙ A} {B∙ : Ty∙ Γ∙ B} {C∙ : Ty∙ Γ∙ C} 
    → {p : A ≡ B} → A∙ ≡Ty[ p ] B∙
    → {q : B ≡ C} → B∙ ≡Ty[ q ] C∙
    → A∙ ≡Ty[ p ∙ q ] C∙
  _∙Ty[]_ {Γ∙} {p} p∙ {q} q∙ =
      _∙P_ {B = Ty∙ Γ∙} p∙ q∙

  ∙Ty[-]-syntax
    : {A B C : Ty Γ} (p : A ≡ B) {q : B ≡ C} {Γ∙ : Ctx∙ Γ}
    → {A∙ : Ty∙ Γ∙ A} {B∙ : Ty∙ Γ∙ B} {C∙ : Ty∙ Γ∙ C} 
    → A∙ ≡Ty[ p ] B∙ → B∙ ≡Ty[ q ] C∙
    → A∙ ≡Ty[ p ∙ q ] C∙
  ∙Ty[-]-syntax _ p∙ q∙ = p∙ ∙Ty[] q∙

  syntax ∙Ty[-]-syntax p p∙ q∙ = p∙ ∙Ty[ p ] q∙ 

  ≡Ty[]⟨⟩-syntax
    : {A B C : Ty Γ} {p : A ≡ B} {q : B ≡ C} {Γ∙ : Ctx∙ Γ}
    → (A∙ : Ty∙ Γ∙ A) {B∙ : Ty∙ Γ∙ B} {C∙ : Ty∙ Γ∙ C}
    → B∙ ≡Ty[ q ] C∙ → A∙ ≡Ty[ p ] B∙
    → A∙ ≡Ty[ p ∙ q ] C∙
  ≡Ty[]⟨⟩-syntax A∙ q∙ p∙ = p∙ ∙Ty[] q∙ 

  syntax ≡Ty[]⟨⟩-syntax A∙ q∙ p∙ = A∙ ≡Ty[]⟨ p∙ ⟩ q∙

  ≡Ty[-]⟨⟩-syntax 
    : {A B C : Ty Γ} {Γ∙ : Ctx∙ Γ} (p : A ≡ B) {q : B ≡ C}
    → (A∙ : Ty∙ Γ∙ A) {B∙ : Ty∙ Γ∙ B} {C∙ : Ty∙ Γ∙ C} 
    → B∙ ≡Ty[ q ] C∙ → A∙ ≡Ty[ p ] B∙
    → A∙ ≡Ty[ p ∙ q ] C∙
  ≡Ty[-]⟨⟩-syntax A∙ p q∙ p∙ = p∙ ∙Ty[] q∙

  syntax ≡Ty[-]⟨⟩-syntax p A∙ q∙ p∙ = A∙ ≡Ty[ p ]⟨ p∙ ⟩ q∙

  beginTy_
    : {p q : A ≡ B}
    → A∙ ≡Ty[ p ] B∙
    → A∙ ≡Ty[ q ] B∙
  beginTy_ {A∙} {B∙} {p} {q} p∙ =
    subst (λ r → A∙ ≡Ty[ r ] B∙) (UIP _ _) p∙ 

  beginTy[_]_
    : ({p} q : A ≡ B)
    → A∙ ≡Ty[ p ] B∙
    → A∙ ≡Ty[ q ] B∙
  beginTy[_]_ {A∙} {B∙} {p} q p∙ =
    subst (λ r → A∙ ≡Ty[ r ] B∙) (UIP _ _) p∙ 

  _∙Sub[]_
    : {p : σ ≡ τ} → σ∙ ≡Sub[ p ] τ∙
    → {q : τ ≡ γ} → τ∙ ≡Sub[ q ] γ∙
    → σ∙ ≡Sub[ p ∙ q ] γ∙
  _∙Sub[]_ {p} p∙ {q} q∙ =
      _∙P_ {B = λ σ → Sub∙ _ _ σ} p∙ q∙

  beginSub_
    : {p q : σ ≡ τ}
    → σ∙ ≡Sub[ p ] τ∙
    → σ∙ ≡Sub[ q ] τ∙
  beginSub_ {σ∙} {τ∙} {p} {q} p∙ =
    subst (λ r → σ∙ ≡Sub[ r ] τ∙) (UIP p q) p∙ 

  beginSub[_]_
    : ({p} q : σ ≡ τ)
    → σ∙ ≡Sub[ p ] τ∙
    → σ∙ ≡Sub[ q ] τ∙
  beginSub[_]_ {σ∙} {τ∙} {p} q p∙ =
    subst (λ r → σ∙ ≡Sub[ r ] τ∙) (UIP p q) p∙ 

  ∙Sub[-]-syntax
    : (p : σ ≡ τ) {q : τ ≡ γ}
    → {σ∙ : Sub∙ Γ∙ Δ∙ σ} {τ∙ : Sub∙ Γ∙ Δ∙ τ} {γ∙ : Sub∙ Γ∙ Δ∙ γ} 
    → σ∙ ≡Sub[ p ] τ∙ → τ∙ ≡Sub[ q ] γ∙
    → σ∙ ≡Sub[ p ∙ q ] γ∙
  ∙Sub[-]-syntax _ p∙ q∙ = p∙ ∙Sub[] q∙

  syntax ∙Sub[-]-syntax p p∙ q∙ = p∙ ∙Sub[ p ] q∙ 

  ≡Sub[]⟨⟩-syntax
    : {p : σ ≡ τ} {q : τ ≡ γ}
    → (σ∙ : Sub∙ Γ∙ Δ∙ σ) {τ∙ : Sub∙ Γ∙ Δ∙ τ} {γ∙ : Sub∙ Γ∙ Δ∙ γ} 
    → τ∙ ≡Sub[ q ] γ∙
    → σ∙ ≡Sub[ p ] τ∙
    → σ∙ ≡Sub[ p ∙ q ] γ∙
  ≡Sub[]⟨⟩-syntax σ∙ q∙ p∙ = p∙ ∙Sub[] q∙ 

  syntax ≡Sub[]⟨⟩-syntax A∙ q∙ p∙ = A∙ ≡Sub[]⟨ p∙ ⟩ q∙

  ≡Sub[-]⟨⟩-syntax 
    : {σ τ γ : Sub Γ Δ} {Γ∙ : Ctx∙ Γ} (p : σ ≡ τ) {q : τ ≡ γ}
    → (σ∙ : Sub∙ Γ∙ Δ∙ σ) {τ∙ : Sub∙ Γ∙ Δ∙ τ} {γ∙ : Sub∙ Γ∙ Δ∙ γ} 
    → τ∙ ≡Sub[ q ] γ∙
    → σ∙ ≡Sub[ p ] τ∙
    → σ∙ ≡Sub[ p ∙ q ] γ∙
  ≡Sub[-]⟨⟩-syntax σ∙ p q∙ p∙ = p∙ ∙Sub[] q∙

  syntax ≡Sub[-]⟨⟩-syntax p σ∙ q∙ p∙ = σ∙ ≡Sub[ p ]⟨ p∙ ⟩ q∙

  _∙Tm[]_
    : {t u v : Tm Γ} {Γ∙ : Ctx∙ Γ} 
    → {t∙ : Tm∙ Γ∙ t} {u∙ : Tm∙ Γ∙ u} {v∙ : Tm∙ Γ∙ v} 
    → {p : t ≡ u} → t∙ ≡Tm[ p ] u∙
    → {q : u ≡ v} → u∙ ≡Tm[ q ] v∙
    → t∙ ≡Tm[ p ∙ q ] v∙
  _∙Tm[]_ {Γ∙} {p} p∙ {q} q∙ =
      _∙P_ {B = Tm∙ Γ∙} p∙ q∙

  ∙Tm[-]-syntax
    : {t u v : Tm Γ} (p : t ≡ u) {q : u ≡ v} {Γ∙ : Ctx∙ Γ}
    → {t∙ : Tm∙ Γ∙ t} {u∙ : Tm∙ Γ∙ u} {v∙ : Tm∙ Γ∙ v} 
    → t∙ ≡Tm[ p ] u∙ → u∙ ≡Tm[ q ] v∙
    → t∙ ≡Tm[ p ∙ q ] v∙
  ∙Tm[-]-syntax _ p∙ q∙ = p∙ ∙Tm[] q∙

  syntax ∙Tm[-]-syntax p p∙ q∙ = p∙ ∙Tm[ p ] q∙ 

  ≡Tm[]⟨⟩-syntax
    : {t u v : Tm Γ} {p : t ≡ u} {q : u ≡ v} {Γ∙ : Ctx∙ Γ}
    → (t∙ : Tm∙ Γ∙ t) {u∙ : Tm∙ Γ∙ u} {v∙ : Tm∙ Γ∙ v} 
    → u∙ ≡Tm[ q ] v∙ → t∙ ≡Tm[ p ] u∙
    → t∙ ≡Tm[ p ∙ q ] v∙
  ≡Tm[]⟨⟩-syntax t∙ q∙ p∙ = p∙ ∙Tm[] q∙ 

  syntax ≡Tm[]⟨⟩-syntax A∙ q∙ p∙ = A∙ ≡Tm[]⟨ p∙ ⟩ q∙

  ≡Tm[-]⟨⟩-syntax 
    : {t u v : Tm Γ} (p : t ≡ u) {q : u ≡ v} {Γ∙ : Ctx∙ Γ}
    → (t∙ : Tm∙ Γ∙ t) {u∙ : Tm∙ Γ∙ u} {v∙ : Tm∙ Γ∙ v} 
    → u∙ ≡Tm[ q ] v∙ → t∙ ≡Tm[ p ] u∙
    → t∙ ≡Tm[ p ∙ q ] v∙
  ≡Tm[-]⟨⟩-syntax A∙ p q∙ p∙ = p∙ ∙Tm[] q∙

  syntax ≡Tm[-]⟨⟩-syntax p A∙ q∙ p∙ = A∙ ≡Tm[ p ]⟨ p∙ ⟩ q∙

  beginTm_
    : {p q : t ≡ u}
    → t∙ ≡Tm[ p ] u∙
    → t∙ ≡Tm[ q ] u∙
  beginTm_ {t∙} {u∙} {p} {q} p∙ =
    subst (t∙ ≡Tm[_] u∙) (UIP _ _) p∙ 

  beginTm[_]_
    : ({p} q : t ≡ u)
    → t∙ ≡Tm[ p ] u∙
    → t∙ ≡Tm[ q ] u∙
  beginTm[_]_ {t∙} {u∙} {p} q p∙ =
    subst (λ r → t∙ ≡Tm[ r ] u∙) (UIP _ _) p∙ 

-- {-
--   ≡Ty[-]⟨⟩-syntax 
--     : {A B C : Ty Γ} {Γ∙ : Ctx∙ Γ} (p : A ≡ B) {q : B ≡ C}
--     → (A∙ : Ty∙ Γ∙ A) {B∙ : Ty∙ Γ∙ B} {C∙ : Ty∙ Γ∙ C} 
--     → B∙ ≡Ty[ q ] C∙ → A∙ ≡Ty[ p ] B∙
--     → A∙ ≡Ty[ p ∙ q ] C∙
--   ≡Ty[-]⟨⟩-syntax A∙ p q∙ p∙ = p∙ ∙Ty[] q∙
--   -}
