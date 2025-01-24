module SC+U+Pi+Id.QIIRT.Coherence where

open import Prelude
  hiding (_,_)

open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties

module RewriteRules where
    {-
      Agda reports that [idS]l fails the local confluence while declaring [idS]l as a rewrite rule, but it can be fixed by declaring idS⇈ as a rewrite rule.
      However, idS⇈ cannot be typed before [idS]l is declared a rewrite rule.

      [idS]l, idS⇈, [⨟]l, ⨟⇈ are proved in SC+U+Pi+Id.QIIRT.Properties
    -}
  postulate
    [idS]l'
      : [ idS ]l Ξ ≡ Ξ
    {-# REWRITE [idS]l' #-}
    idS⇈'
      : idS ⇈ Ξ ≡ idS
    {-# REWRITE idS⇈' #-}
    [⨟]l'
      : [ σ ⨟ τ ]l Ξ ≡ [ σ ]l [ τ ]l Ξ
    {-# REWRITE [⨟]l' #-}
    ⨟⇈'
      : (σ ⨟ τ) ⇈ Ξ ≡ (σ ⇈ ([ τ ]l Ξ)) ⨟ (τ ⇈ Ξ)
    {-# REWRITE ⨟⇈' #-}

  -- sanity check
  _ : [ idS ]l (Ξ , A) ≡ Ξ , A
  _ = refl

  _ : [ σ ⨟ τ ]l (Ξ , A) ≡ [ σ ]l [ τ ]l (Ξ , A)
  _ = refl

coh↑ : (σ τ : Sub Γ Δ) (A : Ty Δ i)
  → σ ≡ τ
  → σ ↑ A ≅ τ ↑ A
coh↑ σ τ A σ=τ = begin
  σ ↑ A ≅⟨ ≡-to-≅ $ ↑=⁺ A σ ⟩
  σ ⁺   ≅⟨ hcong (λ σ → σ ⁺) (≡-to-≅ σ=τ) ⟩
  τ ⁺   ≡⟨ ↑=⁺ A τ ⟨
  τ ↑ A ∎
  where open ≅-Reasoning

-- Coherence property for the term substitution
module _ {Γ Δ : Ctx} {σ γ : Sub Γ Δ} where
  open ≅-Reasoning
  coh[]tm
    : {A : Ty Δ i} {t : Tm Δ A} → σ ≅ γ → [ σ ]t t ≅ [ γ ]t t
  coh[]tm {_} {A} {t} σ=γ = begin
    [ σ ]t  t ≅⟨ ≡-to-≅ $ []tm≡[]t t σ ⟨
    [ σ ]tm t ≅⟨ hcong (λ σ → [ σ ]tm t) σ=γ ⟩
    [ γ ]tm t ≡⟨ []tm≡[]t t γ ⟩
    [ γ ]t  t ∎

{-
  -- WRONG! the coherence of _⇈ Ξ is assumed here  
  coh[⇈]tm
    : (Ξ : Tel Δ) {A : Ty (Δ ⧺ Ξ) i} {t : Tm (Δ ⧺ Ξ) A}
    → σ ≡ γ
    → [ σ ⇈ Ξ ]t t ≅ [ γ ⇈ Ξ ]t t
  coh[⇈]tm Ξ {A} {t} σ=γ = begin
    [ σ ⇈ Ξ ]t  t ≅⟨ ≡-to-≅ $ []tm≡[]t t _ ⟨
    [ σ ⇈ Ξ ]tm t ≅⟨ icong (λ σ → Sub (_ ⧺ [ σ ]l Ξ) (_ ⧺ Ξ)) σ=γ ([_]tm t) (⇈-cong σ=γ Ξ) ⟩
    [ γ ⇈ Ξ ]tm t ≡⟨ []tm≡[]t t _ ⟩
    [ γ ⇈ Ξ ]t  t ∎
-}
  
-- coh[idS⨟]l
--   : (σ : Sub Γ Δ) (Ξ : Tel Δ)
--   → [ idS ⨟ σ ]l Ξ ≡ [ σ ]l Ξ
-- coh[idS⨟]l σ Ξ = begin
--   [ idS ⨟ σ ]l Ξ
--     ≡⟨ [⨟]l idS σ Ξ ⟩
--   [ idS ]l [ σ ]l Ξ
--     ≡⟨ [idS]l ([ σ ]l Ξ) ⟩
--   [ σ ]l Ξ
--     ∎
--   where open ≡-Reasoning

coh-idS⨟⇈
  : (idS ⨟ σ) ⇈ Ξ ≡ σ ⇈ Ξ
coh-idS⨟⇈ = idS⨟ _

coh-⨟idS⇈
  : (σ ⨟ idS) ⇈ Ξ ≡ σ ⇈ Ξ
coh-⨟idS⇈ = _ ⨟idS

coh-⨟-assoc
  : (σ ⨟ (τ ⨟ γ)) ⇈ Ξ ≡ ((σ ⨟ τ) ⨟ γ) ⇈ Ξ
coh-⨟-assoc = ⨟-assoc

coh-[idS⨟]l
  : [ idS ⨟ σ ]l Ξ ≡ [ σ ]l Ξ
coh-[idS⨟]l = refl

coh-[⨟idS]l
  : [ σ ⨟ idS ]l Ξ ≡ [ σ ]l Ξ
coh-[⨟idS]l = refl

coh-[⨟-assoc]l
  : [ (σ ⨟ τ) ⨟ γ ]l Ξ ≡ [ σ ⨟ (τ ⨟ γ) ]l Ξ
coh-[⨟-assoc]l = refl

coh[idS⨟]
  : [ idS ⨟ σ ] A ≡ [ σ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ σ ⨟ idS ] A ≡ [ σ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ (σ ⨟ τ) ⨟ γ ] A ≡ [ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Γ ([ σ ] A)) where
  open ≅-Reasoning
  coh[π₁,]l
    : (Ξ : Tel Δ)
    → [ π₁ (_,_ σ {A} t) ]l Ξ ≡ [ σ ]l Ξ
  coh-π₁,⇈
    : (Ξ : Tel Δ)
    → π₁ (_,_ σ {A} t) ⇈ Ξ ≅ σ ⇈ Ξ
  coh[π₁,⇈]
    : (Ξ : Tel Δ)
    → (B : Ty (Δ ⧺ Ξ) j)
    → [ π₁ (_,_ σ {A} t) ⇈ Ξ ] B ≅ [ σ ⇈ Ξ ] B
  coh[π₁,]l ∅       = refl
  coh[π₁,]l (Ξ , A) = ≅-to-≡ $ hcong₂ _,_ (≡-to-≅ $ coh[π₁,]l Ξ) (coh[π₁,⇈] Ξ A) 

  coh-π₁,⇈ ∅       = ≡-to-≅ π₁,
  coh-π₁,⇈ (Ξ , A) = begin
    π₁ (σ , t) ⇈ Ξ ↑ A ≡⟨ ↑=⁺ A (π₁ (σ , t) ⇈ Ξ) ⟩
    (π₁ (σ , t) ⇈ Ξ) ⁺ ≅⟨ icong (λ Ξ' → Sub (Γ ⧺ Ξ') (Δ ⧺ Ξ)) (coh[π₁,]l Ξ) (λ σ → (_⁺ σ {A})) (coh-π₁,⇈ Ξ) ⟩
    (σ ⇈ Ξ) ⁺          ≡⟨ ↑=⁺ A (σ ⇈ Ξ) ⟨
    σ ⇈ Ξ ↑ A          ∎

  coh[π₁,⇈] Ξ (U i)      = cong-U (hcong (Γ ⧺_) (≡-to-≅ $ coh[π₁,]l Ξ))
  coh[π₁,⇈] Ξ (El x)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) (coh[π₁,]l Ξ)) El (begin
    [ π₁ (σ , t) ⇈ Ξ ]t x  ≡⟨ []tm≡[]t x (π₁ (σ , t) ⇈ Ξ) ⟨
    [ π₁ (σ , t) ⇈ Ξ ]tm x ≅⟨ icong (λ Ξ' → Sub (Γ ⧺ Ξ') (Δ ⧺ _)) (coh[π₁,]l Ξ) ([_]tm x) (coh-π₁,⇈ Ξ) ⟩
    [ σ ⇈ Ξ ]tm x          ≡⟨ []tm≡[]t x (σ ⇈ Ξ) ⟩
    [ σ ⇈ Ξ ]t x           ∎)
  coh[π₁,⇈] Ξ (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) (coh[π₁,]l Ξ)) Lift (coh[π₁,⇈] Ξ B)
  coh[π₁,⇈] Ξ (Π B C)    = {!!}
  coh[π₁,⇈] Ξ (Id a t u) = {!!}


{-
  _⁺ : (σ : Sub Γ Δ) → {A : Ty Δ i} → Sub (Γ , [ σ ] A) (Δ , A)
  _⁺ σ {A} = π₁ idS ⨟ σ , π₂ idS
-}

-- [TODO]: Fix the following coherence proofs.
-- module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) {i : ℕ} (A : Ty Θ i) (t : Tm Δ ([ τ ] A)) where
--   open ≅-Reasoning
--   coh[⨟,]l
--     : (Ξ : Tel (Θ , A))
--     → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
--   coh[⨟,]'
--     : (Ξ : Tel (Θ , A))
--     → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
--     → (B : Ty ((Θ , A) ⧺ Ξ) j)
--     → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]t t) ⇈ Ξ ] B
--   coh[⨟,]l ∅       = refl
--   coh[⨟,]l (Ξ , B) = hcong₂ _,_ (coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) B)

--   coh[⨟,]' Ξ eq (U j)      = cong-U (hcong (Γ ⧺_) eq)
--   coh[⨟,]' Ξ eq (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) (≅-to-≡ eq)) El
--     (coh[⇈]tm Ξ ⨟,)
--   coh[⨟,]' Ξ eq (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Lift (coh[⨟,]' Ξ eq B)
--   coh[⨟,]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
--     (coh[⨟,]' Ξ eq B)
--     (coh[⨟,]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟,]' Ξ eq B)) C)
--   coh[⨟,]' Ξ eq (Id a u v) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Id
--     (coh[⇈]tm Ξ ⨟,) (coh[⇈]tm Ξ ⨟,) (coh[⇈]tm Ξ ⨟,)

--   coh[⨟,]
--     : (Ξ : Tel (Θ , A))
--     → (B : Ty ((Θ , A) ⧺ Ξ) j)
--     → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]t t) ⇈ Ξ ] B
--   coh[⨟,] Ξ B = coh[⨟,]' Ξ (coh[⨟,]l Ξ) B

-- coh[βπ₁] : [ π₁ (σ , t) ] A ≡ [ σ ] A
-- coh[βπ₁] = refl

-- module _ {Γ : Ctx} (σ : Sub Γ ∅) where
--   open ≅-Reasoning

--   coh[η∅]l : (Ξ : Tel ∅)
--     → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
--   coh[η∅]' : (Ξ : Tel ∅)
--     → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
--     → (A : Ty (∅ ⧺ Ξ) i)
--     → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A

--   coh[η∅]l ∅       = refl
--   coh[η∅]l (Ξ , A) = hcong₂ _,_ (coh[η∅]l Ξ) (coh[η∅]' Ξ (coh[η∅]l Ξ) A)

--   coh[η∅]' Ξ eq (U i)      = cong-U (hcong (Γ ⧺_) eq)
--   coh[η∅]' Ξ eq (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) (≅-to-≡ eq)) El (coh[⇈]tm Ξ η∅)
--   coh[η∅]' Ξ eq (Lift A)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Lift (coh[η∅]' Ξ eq A)
--   coh[η∅]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
--     (coh[η∅]' Ξ eq B)
--     (coh[η∅]' (Ξ , B) (hcong₂ _,_ eq (coh[η∅]' Ξ eq B)) C)
--   coh[η∅]' Ξ eq (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Id
--     (coh[⇈]tm Ξ η∅) (coh[⇈]tm Ξ η∅) (coh[⇈]tm Ξ η∅)

--   coh[η∅] : (Ξ : Tel ∅)
--     → (A : Ty (∅ ⧺ Ξ) i)
--     → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A
--   coh[η∅] Ξ A = coh[η∅]' Ξ (coh[η∅]l Ξ) A

-- module _ {Γ Δ : Ctx} {A : Ty Δ i} (σ : Sub Γ (Δ , A)) where
--   open ≅-Reasoning

--   coh[η,]l
--     : (Ξ : Tel (Δ , A)) → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
   
--   coh[η,]'
--     : (Ξ : Tel (Δ , A))
--     → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
--     → (B : Ty ((Δ , A) ⧺ Ξ) j)
--     → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B

--   coh[η,]' Ξ eq (U i)      = cong-U (hcong (Γ ⧺_) eq)
--   coh[η,]' Ξ eq (El u)     = icong  (λ Γ → Tm Γ _) (≅-to-≡ $ hcong (Γ ⧺_) eq) El (coh[⇈]tm Ξ η,)
--   coh[η,]' Ξ eq (Lift B)   = icong  (λ Γ → Ty Γ _) (≅-to-≡ $ hcong (Γ ⧺_) eq) Lift (coh[η,]' Ξ eq B)
--   coh[η,]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
--     (coh[η,]' Ξ eq B)
--     (coh[η,]' (Ξ , B) (hcong₂ _,_ eq (coh[η,]' Ξ eq B)) C)
--   coh[η,]' Ξ eq (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Id
--     (coh[⇈]tm Ξ η,) (coh[⇈]tm Ξ η,) (coh[⇈]tm Ξ η,)

--   coh[η,]l ∅       = refl
--   coh[η,]l (Ξ , A) = hcong₂ _,_ (coh[η,]l Ξ) (coh[η,]' Ξ (coh[η,]l Ξ) A)

--   coh[η,]
--     : (Ξ : Tel (Δ , A)) (B : Ty ((Δ , A) ⧺ Ξ) i)
--     → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B
--   coh[η,] Ξ B = coh[η,]' Ξ (coh[η,]l Ξ) B
