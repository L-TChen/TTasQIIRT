open import Prelude

module Theory.SC.QIIRT-tyOf.StrictSyntaxIso where

open import Theory.SC.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.StrictSyntax
open import Theory.SC.QIIRT-tyOf.Models.Term
  using (Termᵃ; Termᵐ)
import Theory.SC.QIIRT-tyOf.Models.Yoneda as Yoneda
import Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient as Local

open Yoneda Termᵃ Termᵐ
open Local よᵃ よᵐ Ctx-is-set
open Subʸ
open Ty³

postulate
  Tm-is-set : {Γ : Ctx} → isSet (Tm Γ)

◂ᵀ : {Γ : Ctxₛ} → Tyₛ Γ → Ty Γ
◂ᵀ ⟨ E , σ ⟩! = E [ y σ idS ]

◂ᵗ : {Γ : Ctxₛ} → Tmₛ Γ → Tm Γ
◂ᵗ (A , t , p) = t

◂ˢ : {Γ Δ : Ctxₛ} → Subₛ Γ Δ → Sub Γ Δ
◂ˢ σ = y σ idS

◂tyOfₛ : {Γ : Ctxₛ}{A : Tyₛ Γ} → (t : Tmₛ Γ) → tyOfₛ t ≡ A → tyOf (◂ᵗ t) ≡ ◂ᵀ A
◂tyOfₛ (A , t , p) q = p ∙ cong [_]³ q

{-# TERMINATING #-}
◂▸ᶜ : (Γ : Ctx) → ▸ᶜ Γ ≡ Γ
◂▸ᵀ : {Γ : Ctx}(A : Ty Γ) → ◂ᵀ (▸ᵀ A) ≡[ i ⊢ Ty (◂▸ᶜ Γ i) ] A
◂▸ᵗ : {Γ : Ctx}(t : Tm Γ) → ◂ᵗ (▸ᵗ t) ≡[ i ⊢ Tm (◂▸ᶜ Γ i) ] t
◂▸ˢ : {Γ Δ : Ctx}(σ : Sub Γ Δ) → ◂ˢ (▸ˢ σ) ≡[ i ⊢ Sub (◂▸ᶜ Γ i) (◂▸ᶜ Δ i) ] σ
◂▸ᶜ ∅ = refl
◂▸ᶜ (Γ , A) i = ◂▸ᶜ Γ i , ◂▸ᵀ A i
◂▸ᵀ {Γ} (_[_] {Δ = Δ} A σ) = p ◁ pᵈ
  module ◂▸ᵀ[] where
    p : ◂ᵀ (▸ᵀ (A [ σ ])) ≡ E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ idS ] [ y (▸ˢ σ) idS ]
    p = ◂ᵀ (▸ᵀ (A [ σ ]))
        ≡[ i ]⟨ E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ ((idS∘ y (▸ˢ σ) idS) (~ i)) ] ⟩
      E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ (idS ∘ y (▸ˢ σ) idS) ]
        ≡[ i ]⟨ E (▸ᵀ A) [ natʸ ⌜ ▸ᵀ A ⌝ (y (▸ˢ σ) idS) idS (~ i) ] ⟩
      E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ idS ∘ y (▸ˢ σ) idS ]
        ≡⟨ sym ([∘]T _ _ _) ⟩
      E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ idS ] [ y (▸ˢ σ) idS ]
        ∎

    pᵈ : E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ idS ] [ y (▸ˢ σ) idS ] ≡[ i ⊢ Ty (◂▸ᶜ Γ i) ] A [ σ ]
    pᵈ i = ◂▸ᵀ {Δ} A i [ ◂▸ˢ σ i ]

◂▸ᵀ {Γ} U i = U[] {◂▸ᶜ Γ i} {σ = ∅} i
◂▸ᵀ {Γ} ([idS]T {A = A} i) j =
  isSet→SquareP (λ i _ → Ty-is-set {◂▸ᶜ Γ i})
    (λ i → ◂ᵀ (▸ᵀ ([idS]T {A = A} i)))
    [idS]T
    (◂▸ᵀ A)
    (◂▸ᵀ[].p A idS ◁ ◂▸ᵀ[].pᵈ A idS)
    j i
◂▸ᵀ {Γ} ([∘]T A σ τ i) j =
  isSet→SquareP (λ i _ → Ty-is-set {◂▸ᶜ Γ i})
    (λ i → ◂ᵀ (▸ᵀ ([∘]T A σ τ i)))
    ([∘]T A σ τ)
    (◂▸ᵀ[].p (A [ τ ]) σ ◁ ◂▸ᵀ[].pᵈ (A [ τ ]) σ)
    (◂▸ᵀ[].p A (τ ∘ σ) ◁ ◂▸ᵀ[].pᵈ A (τ ∘ σ))
    j i
◂▸ᵀ {Γ} (U[] {σ = σ} i) j =
  isSet→SquareP (λ i _ → Ty-is-set {◂▸ᶜ Γ i})
    (λ i → ◂ᵀ (▸ᵀ (U[] {σ = σ} i)))
    U[]
    (◂▸ᵀ[].p U σ ◁ ◂▸ᵀ[].pᵈ U σ)
    (λ j → U[] {◂▸ᶜ Γ j} {σ = ∅} j)
    j i
◂▸ᵀ {Γ} (Ty-is-set A A' p q i j) k =
  isGroupoid→CubeP (λ i _ _ → Ty (◂▸ᶜ Γ i))
    (λ j i → ◂ᵀ (▸ᵀ (Ty-is-set A A' p q i j)))
    (λ j i → Ty-is-set A A' p q i j)
    (λ k i → ◂▸ᵀ A k)
    (λ k i → ◂▸ᵀ A' k)
    (λ k j → ◂▸ᵀ (p j) k)
    (λ k j → ◂▸ᵀ (q j) k)
    (isSet→isGroupoid Ty-is-set)
    k j i
◂▸ᵗ (t [ σ ]) i = ◂▸ᵗ t i [ ◂▸ˢ σ i ]
◂▸ᵗ (π₂ {A = A} σ) i = π₂ {A = ◂▸ᵀ A i} (◂▸ˢ σ i)
◂▸ᵗ {Γ} (βπ₂ σ t p q i) j =
  isSet→SquareP (λ i _ → Tm-is-set {◂▸ᶜ Γ i})
    (λ i → ◂ᵗ (▸ᵗ (βπ₂ σ t p q i)))
    (βπ₂ σ t p q)
    (◂▸ᵗ (π₂ (σ , t ∶[ p ])))
    (◂▸ᵗ t)
    j i
◂▸ᵗ {Γ} ([idS]t t i) j =
  isSet→SquareP (λ i _ → Tm-is-set {◂▸ᶜ Γ i})
    (λ i → ◂ᵗ (▸ᵗ ([idS]t t i)))
    ([idS]t t)
    (◂▸ᵗ t)
    (◂▸ᵗ (t [ idS ]))
    j i
◂▸ᵗ {Γ} ([∘]t t σ τ i) j =
  isSet→SquareP (λ i _ → Tm-is-set {◂▸ᶜ Γ i})
    (λ i → ◂ᵗ (▸ᵗ ([∘]t t σ τ i)))
    ([∘]t t σ τ)
    (◂▸ᵗ (t [ τ ] [ σ ]))
    (◂▸ᵗ (t [ τ ∘ σ ]))
    j i
◂▸ˢ {Γ} ∅ i = ∅ {◂▸ᶜ Γ i}
◂▸ˢ {Γ} (_,_∶[_] {Δ = Δ} {A = A} σ t p) i =
  _,_∶[_] {A = ◂▸ᵀ A i} (◂▸ˢ σ i) ((sym ([idS]t (◂ᵗ (▸ᵗ t))) ◁ ◂▸ᵗ t) i)
    (isProp→PathP (λ i → Ty-is-set {◂▸ᶜ Γ i} (tyOf ((sym ([idS]t (◂ᵗ (▸ᵗ t))) ◁ ◂▸ᵗ t) i))
      (◂▸ᵀ A i [ ◂▸ˢ σ i ])) q p i)
  where
    p' : tyOf {▸ᶜ Γ} (fst (snd (▸ᵗ t))) ≡ E (▸ᵀ A) [ y ⌜ ▸ᵀ A ⌝ idS ] [ y (▸ˢ σ) idS ]
    p' = snd (snd (▸ᵗ t))
        ∙ cong [_]³ (▸tyOf t p)
        ∙ sym ([∘]Tʸ (E (▸ᵀ A)) (▸ˢ σ) ⌜ ▸ᵀ A ⌝)

    q : _≡_ {A = Ty (▸ᶜ Γ)}
          (tyOf (◂ᵗ (▸ᵗ t)) [ idS ])
          (◂ᵀ (▸ᵀ A) [ ◂ˢ (▸ˢ σ) ])
    q = refl
      ∙ (λ i → p' i [ idS ])
      ∙ [∘]T [ ▸ᵀ A ]³ idS (y (▸ˢ σ) idS)
      ∙ λ i → [ ▸ᵀ A ]³ [ (natʸ (▸ˢ σ) idS idS ∙ cong (y (▸ˢ σ)) (idS∘ idS)) i ]
◂▸ˢ {Γ} idS i = idS {◂▸ᶜ Γ i}
◂▸ˢ (σ ∘ τ) = sym (Subʸ-τidS∘ (▸ˢ σ) (y (▸ˢ τ) idS)) ◁ λ i → ◂▸ˢ σ i ∘ ◂▸ˢ τ i
◂▸ˢ (π₁ {A = A} σ) i = π₁ {A = ◂▸ᵀ A i} (◂▸ˢ σ i)
◂▸ˢ {Γ} {Δ} (βπ₁ σ t p i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {◂▸ᶜ Δ i})
    (λ i → ◂ˢ (▸ˢ (βπ₁ σ t p i)))
    (βπ₁ σ t p)
    (◂▸ˢ (π₁ (σ , t ∶[ p ])))
    (◂▸ˢ σ)
    j i
◂▸ˢ {Γ} {Δ} ((idS∘ σ) i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {◂▸ᶜ Δ i})
    refl
    (idS∘ σ)
    (◂▸ˢ (idS ∘ σ))
    (◂▸ˢ σ)
    j i
◂▸ˢ {Γ} {Δ} ((σ ∘idS) i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {◂▸ᶜ Δ i})
    (λ i → ◂ˢ (▸ˢ ((σ ∘idS) i)))
    (σ ∘idS)
    (◂▸ˢ (σ ∘ idS))
    (◂▸ˢ σ)
    j i
◂▸ˢ (assocS {Γ} {Δ} {Θ} {Ξ} σ τ γ i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {◂▸ᶜ Ξ i})
    refl
    (assocS σ τ γ)
    (◂▸ˢ ((γ ∘ τ) ∘ σ))
    (◂▸ˢ (γ ∘ (τ ∘ σ)))
    j i
◂▸ˢ {Γ} {Θ , A} (,∘ σ t τ p q i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {◂▸ᶜ Θ i , ◂▸ᵀ A i})
    (λ i → ◂ˢ (▸ˢ (,∘ σ t τ p q i)))
    (,∘ σ t τ p q)
    (◂▸ˢ ((σ , t ∶[ p ]) ∘ τ))
    (◂▸ˢ (σ ∘ τ , t [ τ ] ∶[ q ]))
    j i
◂▸ˢ {Γ} (η∅ σ i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {∅})
    (λ i → ◂ˢ (▸ˢ (η∅ σ i)))
    (η∅ σ)
    (◂▸ˢ σ)
    (λ _ → ∅)
    j i
◂▸ˢ {Γ} {Δ , A} (ηπ σ i) j =
  isSet→SquareP (λ i _ → Sub-is-set {◂▸ᶜ Γ i} {◂▸ᶜ (Δ , A) i})
    (λ i → ◂ˢ (▸ˢ (ηπ σ i)))
    (ηπ σ)
    (◂▸ˢ σ)
    (◂▸ˢ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ]))
    j i
◂▸ˢ {Γ} {Δ} (Sub-is-set σ σ' p q i j) k =
  isGroupoid→CubeP (λ i _ _ → Sub (◂▸ᶜ Γ i) (◂▸ᶜ Δ i))
    (λ j i → ◂ˢ (▸ˢ (Sub-is-set σ σ' p q i j)))
    (λ j i → Sub-is-set σ σ' p q i j)
    (λ k i → ◂▸ˢ σ k)
    (λ k i → ◂▸ˢ σ' k)
    (λ k j → ◂▸ˢ (p j) k)
    (λ k j → ◂▸ˢ (q j) k)
    (isSet→isGroupoid Sub-is-set)
    k j i

▸ᵀ≡→≡ : ∀{Γ}{A A' : Ty Γ} → ▸ᵀ A ≡ ▸ᵀ A' → A ≡ A'
▸ᵀ≡→≡ {Γ} {A} {A'} p =
    sym (transportRefl A)
  ∙ (λ i → transport (UIP refl (sym (cong Ty (◂▸ᶜ Γ)) ∙ (cong Ty (◂▸ᶜ Γ))) i) A)
  ∙ fromPathP (compPathP (symP (◂▸ᵀ A) ▷ cong ◂ᵀ p) (◂▸ᵀ A'))

infixr 2 step-▸ᵀ≡
step-▸ᵀ≡ : ∀{Γ A' A''}(A : Ty Γ) → A' ≡ A'' → ▸ᵀ A ≡ ▸ᵀ A' → A ≡ A''
step-▸ᵀ≡ A p ▸p = ▸ᵀ≡→≡ ▸p ∙ p
syntax step-▸ᵀ≡ A p ▸p = A ▸ᵀ≡⟨ ▸p ⟩ p

▸ᵗ≡→≡ : ∀{Γ}{t t' : Tm Γ} → ▸ᵗ t ≡ ▸ᵗ t' → t ≡ t'
▸ᵗ≡→≡ {Γ} {t} {t'} p =
    sym (transportRefl t)
  ∙ (λ i → transport (UIP refl (sym (cong Tm (◂▸ᶜ Γ)) ∙ (cong Tm (◂▸ᶜ Γ))) i) t)
  ∙ fromPathP (compPathP (symP (◂▸ᵗ t) ▷ cong ◂ᵗ p) (◂▸ᵗ t'))

infixr 2 step-▸ᵗ≡
step-▸ᵗ≡ : ∀{Γ t' t''}(t : Tm Γ) → t' ≡ t'' → ▸ᵗ t ≡ ▸ᵗ t' → t ≡ t''
step-▸ᵗ≡ t p ▸p = ▸ᵗ≡→≡ ▸p ∙ p
syntax step-▸ᵗ≡ t p ▸p = t ▸ᵗ≡⟨ ▸p ⟩ p

▸ˢ≡ʸ→≡ : ∀{Γ Δ}{σ σ' : Sub Γ Δ} → ▸ˢ σ ≡ʸ ▸ˢ σ' → σ ≡ σ'
▸ˢ≡ʸ→≡ {Γ} {Δ} {σ} {σ'} p =
    sym (transportRefl σ)
  ∙ (λ i → transport (UIP refl ((λ j → Sub (◂▸ᶜ Γ (~ j)) (◂▸ᶜ Δ (~ j))) ∙ (λ j → Sub (◂▸ᶜ Γ j) (◂▸ᶜ Δ j))) i) σ) 
  ∙ fromPathP (compPathP (symP (◂▸ˢ σ) ▷ cong ◂ˢ (≡ʸ→≡ {σʸ = ▸ˢ σ} {▸ˢ σ'} p)) (◂▸ˢ σ'))

infixr 2 step-▸ˢ≡ʸ
step-▸ˢ≡ʸ : ∀{Γ Δ σ' σ''}(σ : Sub Γ Δ) → σ' ≡ σ'' → ▸ˢ σ ≡ʸ ▸ˢ σ' → σ ≡ σ''
step-▸ˢ≡ʸ σ p ▸pʸ = ▸ˢ≡ʸ→≡ ▸pʸ ∙ p
syntax step-▸ˢ≡ʸ σ p ▸pʸ = σ ▸ˢ≡ʸ⟨ ▸pʸ ⟩ p