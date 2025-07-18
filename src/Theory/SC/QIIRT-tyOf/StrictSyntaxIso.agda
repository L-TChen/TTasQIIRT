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
◂▸ˢ σ = {!   !}