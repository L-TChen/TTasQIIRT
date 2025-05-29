-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude

module Theory.SC+El+Pi+B.QIIRT-tyOf.SetModel where

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax

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

⟦_⟧C : Ctx → Set
{-# TERMINATING #-}
⟦_⟧T : {Γ : Ctx} → Ty Γ → ⟦ Γ ⟧C → Set
⟦_⟧t : {Γ : Ctx} → (t : Tm Γ) → (γ : ⟦ Γ ⟧C) → ⟦ tyOf t ⟧T γ
⟦_⟧S : (σ : Sub Γ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C

⟦_,_⟧p : {Γ : Ctx}(t : Tm Γ){A : Ty Γ} → tyOf t ≡ A → {γ : ⟦ Γ ⟧C} → ⟦ tyOf t ⟧T γ → ⟦ A ⟧T γ
⟦ t , p ⟧p {γ = γ} = subst (λ z → ⟦ z ⟧T γ) p

⟦ ∅' ⟧C = Unit
⟦ Γ , A ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] (⟦ A ⟧T γ)

⟦ A [ σ ] ⟧T γ = ⟦ A ⟧T (⟦ σ ⟧S γ)
⟦ U' ⟧T γ = UU
⟦ El' u p ⟧T γ = T (⟦ u , p ⟧p (⟦ u ⟧t γ))
⟦ Π' A B ⟧T γ = (x : ⟦ A ⟧T γ) → ⟦ B ⟧T (γ , x)
⟦ 𝔹' ⟧T γ = Bool
⟦ [idS]T' {A = A} i ⟧T γ = ⟦ A ⟧T γ
⟦ [∘]T' A σ τ i ⟧T γ = ⟦ A ⟧T (⟦ τ ⟧S (⟦ σ ⟧S γ))
⟦ U[]' i ⟧T γ = UU
⟦ El[]' τ u p q i ⟧T γ = T (transp (λ j → foo i j) i0 (⟦ u ⟧t (⟦ τ ⟧S γ)))
 where
  foo : cong (λ z → ⟦ z ⟧T (⟦ τ ⟧S γ)) p ≡ cong (λ z → ⟦ z ⟧T γ) q
  foo = UIP (cong (λ z → ⟦ z ⟧T (⟦ τ ⟧S γ)) p) (cong (λ z → ⟦ z ⟧T γ) q)
⟦ El[]₂' u pu pu' i ⟧T γ = {!!}
⟦ Π[]' {A = A} {B} {σ = σ} i ⟧T γ = (x : ⟦ A ⟧T (⟦ σ ⟧S γ)) → ⟦ B ⟧T (⟦ σ ⟧S γ , transportRefl x (~ i))
⟦ 𝔹[]' i ⟧T γ = Bool
⟦ 𝔹[]₂' i ⟧T γ = Bool
⟦ El𝕓' i ⟧T γ = Bool
⟦ tyOfπ' a pa b pb i ⟧T γ = UU
⟦ Elπ' a pa b pb i ⟧T γ = (x : T (transp (λ i₁ → ⟦ pa i₁ ⟧T γ) i0 (⟦ a ⟧t γ))) → T (transp (λ i₁ → ⟦ pb i₁ ⟧T (γ , x)) i0 (⟦ b ⟧t (γ , x)))
⟦ Ty-is-set A B x y i j ⟧T γ = {!!}


⟦ ∅S' ⟧S γ = ⋆
⟦ σ , t ∶[ p ]' ⟧S γ = (⟦ σ ⟧S γ) , ⟦ t , p ⟧p (⟦ t ⟧t γ)
⟦ idS ⟧S γ = γ
⟦ σ ∘ τ ⟧S γ = ⟦ σ ⟧S (⟦ τ ⟧S γ)
⟦ π₁ σ ⟧S γ = fst (⟦ σ ⟧S γ)
⟦ βπ₁' σ t p i ⟧S γ = ⟦ σ ⟧S γ
⟦ (idS∘' σ) i ⟧S γ = ⟦ σ ⟧S γ
⟦ (σ ∘idS') i ⟧S γ = ⟦ σ ⟧S γ
⟦ assocS' σ τ δ i ⟧S γ = ⟦ δ ⟧S (⟦ τ ⟧S (⟦ σ ⟧S γ))
⟦ ,∘' σ t τ p q i ⟧S γ = ⟦ σ ⟧S (⟦ τ ⟧S γ) , transp (λ j → foo i j) i0 (⟦ t ⟧t (⟦ τ ⟧S γ))
 where
  foo : cong (λ z → ⟦ z ⟧T (⟦ τ ⟧S γ)) p ≡ cong (λ z → ⟦ z ⟧T γ) q
  foo = UIP _ _
⟦ η∅' σ i ⟧S γ = ⋆
⟦ ηπ σ i ⟧S γ = (fst (⟦ σ ⟧S γ)) , transportRefl (⟦ σ ⟧S γ .snd) (~ i)

⟦ t [ σ ] ⟧t γ = ⟦ t ⟧t (⟦ σ ⟧S γ)
⟦ π₂ σ ⟧t γ = snd (⟦ σ ⟧S γ)
⟦ βπ₂' {A = A} σ t p q i ⟧t γ = {!subst {x = p (~ i)} {q i} (λ z → ⟦ z ⟧T γ)  {!!} (subst-filler (λ z → ⟦ z ⟧T γ) p (⟦ t ⟧t γ) (~ i))!}
 where
  foo : PathP (λ i → (⟦ A [ βπ₁' σ t p (~ i) ] ⟧T γ)) {!!} {!!}
  foo = {!!}
-- subst {x = p (~ i)} {q i} (λ z → ⟦ z ⟧T γ)  {!(isProp→PathP (λ i → Ty-is-set (A [ βπ₁' σ t p (~ i) ])  (tyOf t)) (sym p) q)!} (subst-filler (λ z → ⟦ z ⟧T γ) p (⟦ t ⟧t γ) (~ i))
⟦ [idS]t' t i ⟧t γ = ⟦ t ⟧t γ
⟦ [∘]t' t σ τ i ⟧t γ = ⟦ t ⟧t (⟦ τ ⟧S (⟦ σ ⟧S γ))
⟦ app' t p ⟧t (γ , a) = ⟦ t , p ⟧p (⟦ t ⟧t γ) a
⟦ abs' t ⟧t γ = λ x → ⟦ t ⟧t (γ , x)
⟦ abs[]' {σ = σ} t i ⟧t γ = λ x → ⟦ t ⟧t (⟦ σ ⟧S γ , transportRefl x (~ i))
⟦ Πβ' t i ⟧t (γ , a) = {!!}
⟦ Πη' t p i ⟧t γ = {!!}
⟦ tt' ⟧t γ = true
⟦ ff' ⟧t γ = false
⟦ tt[]' i ⟧t γ = true
⟦ ff[]' i ⟧t γ = false
⟦ elim𝔹' P t u pt pu b pb ⟧t γ
 = Bool-elim (λ x → ⟦ P ⟧T (γ , x)) (⟦ t , pt ⟧p (⟦ t ⟧t γ)) (⟦ u , pu ⟧p (⟦ u ⟧t γ)) (⟦ b , pb ⟧p (⟦ b ⟧t γ))
⟦ elim𝔹[]' P t t₁ pt pu t₂ pb pt₂ pu₂ pb₂ x i ⟧t γ = {!!}
⟦ 𝕓' ⟧t γ = bool
⟦ 𝕓[]' i ⟧t γ = bool
⟦ π' a pa b pb ⟧t γ = pi (⟦ a , pa ⟧p (⟦ a ⟧t γ)) λ x → ⟦ b , pb ⟧p (⟦ b ⟧t (γ , x))
⟦ π[]' t pa t₁ pb pa' pb' i ⟧t γ = {!!}
