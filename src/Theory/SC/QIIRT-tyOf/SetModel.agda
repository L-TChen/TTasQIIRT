-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude

module Theory.SC.QIIRT-tyOf.SetModel where

open import Theory.SC.QIIRT-tyOf.Syntax

mutual
  data UU : Set where
    bool : UU
    pi : (a : UU) → (T a → UU) → UU

  T : UU → Set
  T bool = Bool
  T (pi a b) = (x : T a) → T (b x)

Bool-elim : (P : Bool → Set) → P true → P false → (b : Bool) → P b
Bool-elim P t f true = t
Bool-elim P t f false = f

postulate
 UIP : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → isProp (x ≡ y)

transportRefl' : {A : Set} (k : I) → (x : A) → transp (λ i → A) k x ≡ x
transportRefl' {A = A} k x i = transp (λ i → A) (i ∨ k) x

⟦_⟧C : Ctx → Set
{-# TERMINATING #-}
⟦_⟧T : {Γ : Ctx} → Ty Γ → ⟦ Γ ⟧C → Set
⟦_⟧t : {Γ : Ctx} → (t : Tm Γ) → (γ : ⟦ Γ ⟧C) → ⟦ tyOf t ⟧T γ
⟦_⟧S : (σ : Sub Γ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C

⟦_,_⟧p : {Γ : Ctx}(t : Tm Γ){A : Ty Γ} → tyOf t ≡ A → {γ : ⟦ Γ ⟧C} → ⟦ tyOf t ⟧T γ → ⟦ A ⟧T γ
⟦ t , p ⟧p {γ = γ} = transp (λ i → ⟦ p i ⟧T γ) i0

⟦ ∅ ⟧C = Unit
⟦ Γ , A ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] (⟦ A ⟧T γ)

⟦ A [ σ ] ⟧T γ = ⟦ A ⟧T (⟦ σ ⟧S γ)
⟦ U ⟧T γ = UU
⟦ [idS]T {A = A} i ⟧T γ = ⟦ A ⟧T γ
⟦ [∘]T A σ τ i ⟧T γ = ⟦ A ⟧T (⟦ τ ⟧S (⟦ σ ⟧S γ))
⟦ U[] i ⟧T γ = UU
⟦ Ty-is-set A B x y i j ⟧T γ = {!!}


⟦ ∅S ⟧S γ = ⋆
⟦ σ , t ∶[ p ] ⟧S γ = (⟦ σ ⟧S γ) , ⟦ t , p ⟧p (⟦ t ⟧t γ)
⟦ idS ⟧S γ = γ
⟦ σ ∘ τ ⟧S γ = ⟦ σ ⟧S (⟦ τ ⟧S γ)
⟦ π₁ σ ⟧S γ = ⟦ σ ⟧S γ .fst
⟦ βπ₁ σ t p i ⟧S γ = ⟦ σ ⟧S γ
⟦ (idS∘ σ) i ⟧S γ = ⟦ σ ⟧S γ
⟦ (σ ∘idS) i ⟧S γ = ⟦ σ ⟧S γ
⟦ assocS σ τ δ i ⟧S γ = ⟦ δ ⟧S (⟦ τ ⟧S (⟦ σ ⟧S γ))
⟦ ,∘ σ t τ p q i ⟧S γ = ⟦ σ ⟧S (⟦ τ ⟧S γ) , transp (λ j → foo i j) i0 (⟦ t ⟧t (⟦ τ ⟧S γ))
 where
  foo : cong (λ z → ⟦ z ⟧T (⟦ τ ⟧S γ)) p ≡ cong (λ z → ⟦ z ⟧T γ) q
  foo = UIP _ _
⟦ η∅ σ i ⟧S γ = ⋆
⟦ ηπ σ i ⟧S γ = ⟦ σ ⟧S γ .fst , transportRefl (⟦ σ ⟧S γ .snd) (~ i)

⟦ t [ σ ] ⟧t γ = ⟦ t ⟧t (⟦ σ ⟧S γ)
⟦ π₂ σ ⟧t γ = ⟦ σ ⟧S γ .snd
⟦ βπ₂ {A = A} σ t p q i ⟧t γ = {! ⟦ t ⟧t γ !}
-- transp (λ i₁ → ⟦ p i₁ ⟧T γ) i0 (⟦ t ⟧t γ) : ⟦ q i ⟧T γ
-- ⟦ t ⟧t γ :  ⟦ q i ⟧T γ
{-
  bar : PathP (λ i → ⟦ q i ⟧T γ) (transp (λ i₁ → ⟦ p i₁ ⟧T γ) i0 (⟦ t ⟧t γ)) (⟦ t ⟧t γ)
  bar = {!subst (λ z → PathP z (transp (λ i₁ → ⟦ p i₁ ⟧T γ) i0 (⟦ t ⟧t γ)) (⟦ t ⟧t γ)) ? ?!}
  foo : sym p i ≡ q i
  foo = {!sym p i!}
-}
  where -- subst {x = p (~ i)} {q i} (λ z → ⟦ z ⟧T γ) foo (subst-filler (λ z → ⟦ z ⟧T γ) p (⟦ t ⟧t γ) (~ i))
    foo : PathP (λ i → ⟦ p i ⟧T γ)
      (⟦ t ⟧t γ)
      (transp (λ j → ⟦ p j ⟧T γ) i0 (⟦ t ⟧t γ))
    foo = transport-filler (λ j → ⟦ p j ⟧T γ) (⟦ t ⟧t γ)

-- subst {x = p (~ i)} {q i} (λ z → ⟦ z ⟧T γ)  {!(isProp→PathP (λ i → Ty-is-set (A [ βπ₁' σ t p (~ i) ])  (tyOf t)) (sym p) q)!} (subst-filler (λ z → ⟦ z ⟧T γ) p (⟦ t ⟧t γ) (~ i))
⟦ [idS]t t i ⟧t γ   = ⟦ t ⟧t γ
⟦ [∘]t t σ τ i ⟧t γ = ⟦ t ⟧t (⟦ τ ⟧S (⟦ σ ⟧S γ))
