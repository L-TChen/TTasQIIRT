-- [TODO] Use the identity type to define the interface instead.

open import Prelude

module Theory.SC.QIIRT-tyOf.Model.Set where

module _ (UU : Set) where
  open import Theory.SC.QIIRT-tyOf.Syntax
  open Var

  ⟦_⟧C : Ctx → Set

  {-# TERMINATING #-}
  ⟦_⟧T : {Γ : Ctx} → Ty Γ → ⟦ Γ ⟧C → Set
  ⟦_⟧t : {Γ : Ctx} → (t : Tm Γ) → (γ : ⟦ Γ ⟧C) → ⟦ tyOf t ⟧T γ
  ⟦_⟧S : (σ : Sub Γ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C

-- This would look nicer, but does not play well with the termination checker
-- ⟦_,_⟧p : {Γ : Ctx}(t : Tm Γ){A : Ty Γ} → tyOf t ≡ A → {γ : ⟦ Γ ⟧C} → ⟦ tyOf t ⟧T γ → ⟦ A ⟧T γ
-- ⟦ t , p ⟧p {γ = γ} = transport (λ i → ⟦ p i ⟧T γ)

  ⟦ ∅     ⟧C = Unit
  ⟦ Γ , A ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] (⟦ A ⟧T γ)

  ⟦ A [ σ ]          ⟧T γ = ⟦ A ⟧T (⟦ σ ⟧S γ)
  ⟦ U                ⟧T γ = UU
  ⟦ [idS]T {A = A} i ⟧T γ = ⟦ A ⟧T γ
  ⟦ [∘]T A σ τ i     ⟧T γ = ⟦ A ⟧T (⟦ τ ⟧S (⟦ σ ⟧S γ))
  ⟦ U[] i            ⟧T γ = UU
--  ⟦ Ty-is-set A B x y i j ⟧T γ =
--    isSet→SquareP (λ _ _ → λ X Y → UIP)
--      (λ i → ⟦ x i ⟧T γ)
--      (λ i → ⟦ y i ⟧T γ)
--      refl
--      refl
--      i j

  ⟦ ∅              ⟧S γ = ⋆
  ⟦ σ , t ∶[ p ]   ⟧S γ = ⟦ σ ⟧S γ , transport (λ i → ⟦ p i ⟧T γ) (⟦ t ⟧t γ)
  ⟦ idS            ⟧S γ = γ
  ⟦ σ ∘ τ          ⟧S γ = ⟦ σ ⟧S (⟦ τ ⟧S γ)
  ⟦ π₁ σ           ⟧S γ = ⟦ σ ⟧S γ .fst
  ⟦ βπ₁ σ t p i    ⟧S γ = ⟦ σ ⟧S γ
  ⟦ (idS∘ σ) i     ⟧S γ = ⟦ σ ⟧S γ
  ⟦ (σ ∘idS) i     ⟧S γ = ⟦ σ ⟧S γ
  ⟦ assocS σ τ δ i ⟧S γ = ⟦ δ ⟧S (⟦ τ ⟧S (⟦ σ ⟧S γ))
  ⟦ ,∘ σ t τ p q i ⟧S γ = ⟦ σ ⟧S (⟦ τ ⟧S γ) , transport (λ j → foo i j) (⟦ t ⟧t (⟦ τ ⟧S γ))
    where
      foo : (λ i → ⟦ p i ⟧T (⟦ τ ⟧S γ)) ≡ (λ i → ⟦ q i ⟧T γ)
      foo = UIP _ _
  ⟦ η∅ σ i         ⟧S γ = ⋆
  ⟦ ηπ σ i         ⟧S γ = ⟦ σ ⟧S γ .fst , transportRefl (⟦ σ ⟧S γ .snd) (~ i)
 --  ⟦ Sub-is-set σ τ p q i j ⟧S γ =
 --    isSet→SquareP (λ _ _ → λ _ _ → UIP) (λ i → ⟦ p i ⟧S γ) (λ i → ⟦ q i ⟧S γ) refl refl i j

  ⟦ t [ σ ] ⟧t γ = ⟦ t ⟧t (⟦ σ ⟧S γ)
  ⟦ π₂ σ    ⟧t γ = ⟦ σ ⟧S γ .snd
  ⟦ βπ₂ {A = A} σ t p q i ⟧t γ = goal i
    where
      goal : PathP (λ i → ⟦ q i ⟧T γ) (transport (λ i₁ → ⟦ p i₁ ⟧T γ) (⟦ t ⟧t γ)) (⟦ t ⟧t γ)
      goal = toPathP goal'
        where
          baz : transport (λ j → ⟦ q j ⟧T γ) (transport (λ j → ⟦ p j ⟧T γ) (⟦ t ⟧t γ)) ≡ transport (λ j → ⟦ p (~ j) ⟧T γ) (transport (λ j → ⟦ p j ⟧T γ) (⟦ t ⟧t γ))
          baz j = transport (UIP (λ j → ⟦ q j ⟧T γ) (λ j → ⟦ p (~ j) ⟧T γ) j) (transport (λ j → ⟦ p j ⟧T γ) (⟦ t ⟧t γ))
          goal' : transport (λ i → ⟦ q i ⟧T γ) (transport (λ i → ⟦ p i ⟧T γ) (⟦ t ⟧t γ)) ≡ ⟦ t ⟧t γ
          goal' = baz ∙ fromPathP (λ i → transport-filler (λ i → ⟦ p i ⟧T γ) (⟦ t ⟧t γ) (~ i))

  ⟦ [idS]t t i   ⟧t γ = ⟦ t ⟧t γ
  ⟦ [∘]t t σ τ i ⟧t γ = ⟦ t ⟧t (⟦ τ ⟧S (⟦ σ ⟧S γ))
 --  ⟦ Tm-is-set t u p q i j ⟧t γ = UIP (cong (λ t → ⟦ t ⟧t γ) {!p!}) (cong (λ t → ⟦ t ⟧t γ) {!!}) i j  


module _ (UU : Set) where
  open import Theory.SC.QIIRT-tyOf.Model
  
  stdMot : Motive
  stdMot = record
      { Ctx  = Set
      ; Ty   = λ Γ → (Γ → Set)
      ; Sub  = λ Γ Δ → Γ → Δ
      ; Tm   = λ Γ → Σ[ A ∈ (Γ → Set) ] ((γ : Γ) → A γ)
      ; tyOf = λ (A , t) γ → A γ
  --    ; Tyᴬ-is-set = λ _ _ → UIP
  --    ; Tmᴬ-is-set = λ {_} → isSetΣ (isSetΠ (λ γ → λ _ _ → UIP)) (λ A → isSetΠ (λ γ → λ _ _ → UIP))
  --    ; Subᴬ-is-set = isSetΠ (λ γ → λ _ _ → UIP)
      }

  open IsSC
  
  stdModelSC : IsSC stdMot
  stdModelSC .∅               = Unit
  stdModelSC ._,C_ Γ A        = Σ Γ A
  stdModelSC ._[_]T A σ γ     = A (σ γ)
  stdModelSC ._[_]t (A , t) σ =
    (λ γ → A (σ γ)) , λ γ → t (σ γ)
  stdModelSC .tyOf[]         = refl
  stdModelSC .∅S      γ      = ⋆
  stdModelSC ._,_∶[_] σ (A , t) p γ =
    σ γ , transport (λ i → p i γ) (t γ)
  stdModelSC .idS     γ      = γ
  stdModelSC ._∘_     τ σ γ  = τ (σ γ)
  stdModelSC .π₁      σ γ    = σ γ .fst
  stdModelSC .π₂ {A = A} σ   = (λ γ → A (σ γ .fst)) , λ γ → σ γ .snd
  stdModelSC .tyOfπ₂  _      = refl
  stdModelSC .idS∘_   _      = refl
  stdModelSC ._∘idS   _      = refl
  stdModelSC .assocS  _ _ _  = refl
  stdModelSC .[idS]T         = refl
  stdModelSC .[∘]T    _ _ _  = refl
  stdModelSC .,∘ {Δ} {Θ} {Γ} {A} σ (B , t) τ p q i γ =
    σ (τ γ) , transport (UIP (λ j → p j (τ γ)) (λ j → q j γ) i) (t (τ γ))
-- The following is ideal, but it does not work well with Agda's termination checker.
--    σ (τ γ) , foo γ (~ i) -- [TODO] Why does it trigger the termination checker? 
--    where
--    foo : (γ : Γ) →
--      transport (λ _ → A (σ (τ γ))) _ ≡ transport (λ j → p j (τ γ)) (t (τ γ))
--    foo γ =
--      transportRefl _  ∙ transportRefl _ ∙ transportRefl _ ∙ 
--       (λ i → transport (λ j → p j (τ γ)) (transportRefl (transport (λ _ → B (τ γ)) (transport (λ _ → B (τ γ)) (t (τ γ)))) i)) ∙
--       (λ i → transport (λ j → p j (τ γ)) (transportRefl (transport (λ _ → B (τ γ)) (t (τ γ))) i)) ∙
--        (λ i → transport (λ j → p j (τ γ)) (transportRefl (t (τ γ)) i))

  stdModelSC .ηπ  {Γ} {Δ} {A} σ i =
    λ γ → σ γ .fst , transport-filler (λ j → A (σ γ .fst)) (σ γ .snd) i
  stdModelSC .η∅      _     = refl
  stdModelSC .βπ₁     _ _ _ = refl
  stdModelSC .βπ₂ {Γ} σ (A , t) p i =
    (λ γ → p (~ i) γ) , λ γ → transport-filler (λ j → p j γ) (t γ) (~ i)
  stdModelSC .[idS]t  _     = refl
  stdModelSC .[∘]t    _ _ _ = refl
  stdModelSC .U       _     = UU
  stdModelSC .U[]           = refl

  stdModel : SC _ _ _ _
  stdModel = record
    { mot = stdMot
    ; isSC = stdModelSC
    }
