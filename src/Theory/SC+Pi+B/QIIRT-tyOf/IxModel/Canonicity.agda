open import Prelude

module Theory.SC+Pi+B.QIIRT-tyOf.IxModel.Canonicity where

open import Cubical.Data.Sum

-- open import Theory.SC+Pi+B.QIIRT-tyOf.Syntax
-- open Var

open import Theory.SC+Pi+B.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model.Term
open import Theory.SC.QIIRT-tyOf.DisplayedModel
open import Theory.SC+Pi+B.QIIRT-tyOf.DisplayedModel

open import Theory.SC+Pi+B.QIIRT-tyOf.DisplayedModel Term

open SC+Pi+B Term
open Var

Ctxᴳ : Ctx → Set₁
Ctxᴳ Γ = Sub ∅ Γ → Set

Subᴳ : Ctxᴳ Γ → Ctxᴳ Δ → Sub Γ Δ → Set
Subᴳ {Γ} {Δ} Γ∙ Δ∙ σ =
  (γ : Sub ∅ Γ) → Γ∙ γ → Δ∙ (σ ∘ γ)

Tyᴳ : Ctxᴳ Γ → Ty Γ → Set₁
Tyᴳ {Γ} Γ∙ A = (γ : Sub ∅ Γ) (γ∙ : Γ∙ γ) (t : Tm ∅) → tyOf t ≡ A [ γ ]T → Set

Tmᴳ : Ctxᴳ Γ → Tm Γ → Set₁
Tmᴳ {Γ} Γ∙ t = (γ : Sub ∅ Γ)(γ∙ : Γ∙ γ) → 
  Σ[ A∙ ∈ Tyᴳ Γ∙ (tyOf t) ] A∙ γ γ∙ (t [ γ ]t) refl 

tyOfᴳ : {Γᴳ : Ctxᴳ Γ} → Tmᴳ Γᴳ t → Tyᴳ Γᴳ (tyOf t)
tyOfᴳ {Γ} {t} {Γᴳ} t∙ γ γ∙ t' p = t∙ γ γ∙ .fst γ γ∙ t' p

𝔹ᴳ : {Γᴳ : Ctxᴳ Γ} → Tyᴳ Γᴳ 𝔹
𝔹ᴳ γ γᴳ t _ = (t ≡ tt) ⊎ (t ≡ ff)

tt∙ : {Γᴳ : Ctxᴳ Γ} → Tmᴳ Γᴳ tt
tt∙ γ γ∙ = 𝔹ᴳ , inl (tt[] γ)

ff∙ : {Γᴳ : Ctxᴳ Γ} → Tmᴳ Γᴳ ff
ff∙ γ γ∙ = 𝔹ᴳ , inr (ff[] γ)

CanonMot∙ : Motive∙ TermSC _ _ _ _
CanonMot∙ = record
    { Ctx∙  = Ctxᴳ
    ; Ty∙   = Tyᴳ
    ; Sub∙  = Subᴳ
    ; Tm∙   = Tmᴳ
    ; tyOf∙ = tyOfᴳ
    }

CanonisSC : IsSC∙ TermSC CanonMot∙
CanonisSC = record
  { ∅∙     = λ _ → Unit
  ; _,∙_   = λ Γ∙ A∙ γa →
      Σ[ γ∙ ∈ Γ∙ (π₁ {A = _} idS ∘ γa) ] A∙ (π₁ idS ∘ γa) γ∙ (π₂ idS [ γa ]t) ([∘]T _ _ _)
  ; _∘∙_   = λ {Δ} {Δ∙} {Θ} {Θ∙} {τ} {Γ} {Γ∙} {σ} σ∙ τ∙ γ γ∙ →
      subst Θ∙ (sym $ assocS _ _ _) (σ∙ (σ ∘ γ) (τ∙ γ γ∙))
  ; idS∙   = λ {Γ∙ = Γ∙} σ σ∙ → subst Γ∙ (sym $ idS∘ σ) σ∙
  ; _∘idS∙ = λ σ∙ → {!!}
  ; idS∘∙_ = λ σ∙ → {!!}
  }
-- --   ; _[_]T∙ = {!!}
-- --   ; _[_]t∙ = {!!}
-- --   ; tyOf[]∙ = {!!}
-- --   ; ∅S∙ = {!!}
-- --   ; _,_∶[_,_]∙ = {!!}
-- --   ; idS∙ = {!!}
-- --   ; _∘∙_ = {!!}
-- --   ; π₁∙ = {!!}
-- --   ; π₂∙ = {!!}
-- --   ; tyOfπ₂∙ = {!!}
-- --   ; idS∘∙_ = {!!}
-- --   ; _∘idS∙ = {!!}
-- --   ; assocS∙ = {!!}
-- --   ; ,∘∙ = {!!}
-- --   ; ηπ∙ = {!!}
-- --   ; η∅∙ = {!!}
-- --   ; βπ₁∙ = {!!}
-- --   ; βπ₂∙ = {!!}
-- --   ; [idS]T∙ = {!!}
-- --   ; [∘]T∙ = {!!}
-- --   ; [idS]t∙ = {!!}
-- --   ; [∘]t∙ = {!!}
-- --   ; U∙ = {!!}
-- --   ; U[]∙ = {!!}
-- --   }

-- -- -- ∅ᴳ : Ctxᴳ ∅
-- -- -- ∅ᴳ _ = Unit

-- -- -- _,ᴳ_ : (Γᴳ : Ctxᴳ Γ) → Tyᴳ Γᴳ A → Ctxᴳ (Γ , A)
-- -- -- Γᴳ ,ᴳ Aᴳ = λ γ → Σ[ γᴳ ∈ Γᴳ (π₁ γ) ] Aᴳ (π₁ γ) γᴳ (π₂ γ)

-- -- -- _[_]Tᴳ
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}
-- -- --   → Tyᴳ Δᴳ A → Subᴳ Γᴳ Δᴳ σ → Tyᴳ Γᴳ (A [ σ ])
-- -- -- _[_]Tᴳ {σ = σ} Aᴳ σᴳ = λ γ γᴳ → Aᴳ (σ ∘ γ) (σᴳ γ γᴳ)

-- -- -- _[_]tᴳ
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}
-- -- --   → Tmᴳ Δᴳ t → Subᴳ Γᴳ Δᴳ σ → Tmᴳ Γᴳ (t [ σ ])
-- -- -- _[_]tᴳ {t = t} {σ} tᴳ σᴳ = λ γ γᴳ
-- -- --   → tyOf t [ σ ] , _[_]Tᴳ {A = tyOf t} (tyOfᴳ tᴳ) σᴳ , refl ,
-- -- --     let (A , Aᴳ , p , aᴳ) = tᴳ (σ ∘ γ) (σᴳ γ γᴳ)
-- -- --     in sym ([∘]t _ _ _) , transport (λ i → Aᴳ (σ ∘ γ) (σᴳ γ γᴳ) ([∘]t t γ σ (~ i))) aᴳ

-- -- -- ∅Sᴳ : {Γᴳ : Ctxᴳ Γ} → Subᴳ Γᴳ ∅ᴳ ∅
-- -- -- ∅Sᴳ _ _ = ⋆

-- -- -- _∘ᴳ_
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Θᴳ : Ctxᴳ Θ}
-- -- --   → Subᴳ Δᴳ Θᴳ σ → Subᴳ Γᴳ Δᴳ τ
-- -- --   → Subᴳ Γᴳ Θᴳ (σ ∘ τ)
-- -- -- _∘ᴳ_ {σ = σ} {τ} {Θᴳ = Θᴳ} σᴳ τᴳ γ γᴳ = transport (λ i → Θᴳ (assocS γ τ σ (~ i))) (σᴳ (τ ∘ γ) (τᴳ γ γᴳ))

-- -- -- idSᴳ : {Γᴳ : Ctxᴳ Γ} → Subᴳ Γᴳ Γᴳ idS
-- -- -- idSᴳ {Γᴳ = Γᴳ} γ γᴳ = transport (λ i → Γᴳ ((idS∘ γ) (~ i))) γᴳ

-- -- -- π₁ᴳ
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Aᴳ : Tyᴳ Δᴳ A}
-- -- --   → Subᴳ Γᴳ (Δᴳ ,ᴳ Aᴳ) σ
-- -- --   → Subᴳ Γᴳ Δᴳ (π₁ σ)
-- -- -- π₁ᴳ {σ = σ} {Δᴳ = Δᴳ} σᴳ γ γᴳ = let (δᴳ , _) = σᴳ γ γᴳ in transport (λ i → Δᴳ (π₁∘ σ γ i)) δᴳ

-- -- -- π₂ᴳ
-- -- --   : {σ : Sub Γ (Δ , A)}{Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Aᴳ : Tyᴳ Δᴳ A}
-- -- --   → Subᴳ Γᴳ (Δᴳ ,ᴳ Aᴳ) σ
-- -- --   → Tmᴳ Γᴳ (π₂ σ)
-- -- -- π₂ᴳ {A = A} {σ = σ} {Δᴳ = Δᴳ} {Aᴳ} σᴳ γ γᴳ =
-- -- --   A [ π₁ σ ] , _[_]Tᴳ {A = A} Aᴳ (π₁ᴳ {A = A} {Aᴳ = Aᴳ} σᴳ) , refl ,
-- -- --   let (δᴳ , aᴳ) = σᴳ γ γᴳ
-- -- --   in transport (λ i → Aᴳ (π₁∘ σ γ i) {!   !} (π₂∘ σ γ i)) aᴳ

-- -- -- _,ᴳ_∶[_∣_]
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Aᴳ : Tyᴳ Δᴳ A}
-- -- --   → (σᴳ : Subᴳ Γᴳ Δᴳ σ)(tᴳ : Tmᴳ Γᴳ t)(p : tyOf t ≡ A [ σ ]) → tyOfᴳ tᴳ ≡ _[_]Tᴳ {A = A} Aᴳ σᴳ
-- -- --   → Subᴳ Γᴳ (Δᴳ ,ᴳ Aᴳ) (σ , t ∶[ p ])
-- -- -- _,ᴳ_∶[_∣_] {Γ} {Δ} {A} {σ} {t} {Γᴳ} {Δᴳ} {Aᴳ} σᴳ tᴳ p pᴳ γ γᴳ =
-- -- --   transport (cong Δᴳ (sym (cong π₁ (⟨,∘⟩ σ t γ p) ∙ βπ₁ (σ ∘ γ) _ _))) (σᴳ γ γᴳ) ,
-- -- --   {!   !}

-- -- -- _↑ᴳ_
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}(σᴳ : Subᴳ Γᴳ Δᴳ σ)(Aᴳ : Tyᴳ Δᴳ A)
-- -- --   → Subᴳ (Γᴳ ,ᴳ _[_]Tᴳ {A = A} Aᴳ σᴳ) (Δᴳ ,ᴳ Aᴳ) (σ ↑ A)
-- -- -- _↑ᴳ_ {Γ} {Δ} {σ} {A} {Γᴳ} {Δᴳ} σᴳ Aᴳ =
-- -- --   _,ᴳ_∶[_∣_] {Γ , A [ σ ]} {Δ} {A} {σ ∘ π₁ idS} {π₂ idS} {Γᴳ ,ᴳ _[_]Tᴳ {A = A} Aᴳ σᴳ} {Δᴳ} {Aᴳ}
-- -- --     (_∘ᴳ_ {Θᴳ = Δᴳ} σᴳ (π₁ᴳ {A = A [ σ ]} {Aᴳ = _[_]Tᴳ {A = A} Aᴳ σᴳ} idSᴳ))
-- -- --     (π₂ᴳ {Aᴳ = _[_]Tᴳ {A = A} Aᴳ σᴳ} idSᴳ)
-- -- --     ([∘]T A (π₁ idS) σ)
-- -- --     {!   !}

-- -- -- Πᴳ
-- -- --   : {Γᴳ : Ctxᴳ Γ}
-- -- --   → (Aᴳ : Tyᴳ Γᴳ A)(Bᴳ : Tyᴳ (Γᴳ ,ᴳ Aᴳ) B)
-- -- --   → Tyᴳ Γᴳ (Π A B)
-- -- -- Πᴳ {Γ} {A} {B} {Γᴳ} Aᴳ Bᴳ γ γᴳ t =
-- -- --   Σ[ p ∈ tyOf t ≡ Π (A [ γ ]) (B [ γ ↑ A ]) ]
-- -- --   ((a : Tm ∅)(q : tyOf a ≡ A [ γ ])(aᴳ : Aᴳ γ γᴳ a)
-- -- --   → Bᴳ (_∘_ {∅ , A [ γ ]} {Γ , A} {∅} (γ ↑ A) (idS , a ∶[ q ∙ [idS]T ]))
-- -- --        (_∘ᴳ_ {∅} {∅ , A [ γ ]} {Γ , A} {γ ↑ A} {idS , a ∶[ q ∙ [idS]T ]} {∅ᴳ}
-- -- --              (_↑ᴳ_ {σ = γ} (λ γ' _ → transport (λ i → Γᴳ ((sym (γ ∘idS) ∙ (λ j → γ ∘ (η∅ idS ∙ sym (η∅ γ')) j)) i)) γᴳ) Aᴳ)
-- -- --              {!   !} idS ⋆)
-- -- --        (app t p [ idS , a ∶[ q ∙ [idS]T ] ])
-- -- --   )

-- -- -- appᴳ
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Aᴳ : Tyᴳ Γᴳ A}{Bᴳ : Tyᴳ (Γᴳ ,ᴳ Aᴳ) B}
-- -- --   → (tᴳ : Tmᴳ Γᴳ t)(p : tyOf t ≡ Π A B) → tyOfᴳ tᴳ ≡[ i ⊢ Tyᴳ Γᴳ (p i) ] Πᴳ {A = A} {B = B} Aᴳ Bᴳ
-- -- --   → Tmᴳ (Γᴳ ,ᴳ Aᴳ) (app t p)
-- -- -- appᴳ {A = A} {B} {Bᴳ = Bᴳ} tᴳ p pᴳ γ (π₁γᴳ , _) = B , Bᴳ , refl ,
-- -- --   let (A' , A'ᴳ , q , aᴳ) = tᴳ (π₁ γ) π₁γᴳ
-- -- --   in {!   !}

-- -- -- absᴳ
-- -- --   : {Γᴳ : Ctxᴳ Γ}{Aᴳ : Tyᴳ Γᴳ A}(tᴳ : Tmᴳ {Γ , A} (Γᴳ ,ᴳ Aᴳ) t)
-- -- --   → Tmᴳ Γᴳ (abs t)
-- -- -- absᴳ {A = A} {t = t} {Aᴳ = Aᴳ} tᴳ γ γᴳ = Π A (tyOf t) , Πᴳ {A = A} {B = tyOf t} Aᴳ (tyOfᴳ tᴳ) , (λ _ → Π A (tyOf t)) ,
-- -- --   Π[] {A = A} {B = tyOf t} {σ = γ} , λ a q aᴳ → {!   !}
