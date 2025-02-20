module Theory.SC+U+Pi+Id.QIIRT.Coherence where

open import Prelude
  hiding (_,_)

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Properties


coh↑ : (σ τ : Sub Γ Δ) (A : Ty Δ i)
  → σ ≡ τ
  → σ ↑ A ≅ τ ↑ A
coh↑ σ τ A σ=τ = begin
  σ ↑ A ≅⟨ ≡-to-≅ $ ↑=⁺ A σ ⟩
  σ ⁺   ≅⟨ hcong (λ σ → σ ⁺) (≡-to-≅ σ=τ) ⟩
  τ ⁺   ≡⟨ ↑=⁺ A τ ⟨
  τ ↑ A ∎
  where open ≅-Reasoning

module _ {Γ Γ' Δ : Ctx} {σ : Sub Γ Δ} {σ' : Sub Γ' Δ} (A : Ty Δ i) where
  coh-congCtx-↑
    : (Γ=Γ' : Γ ≡ Γ')
    → σ ≅ σ'
    → σ ↑ A ≅ σ' ↑ A
  coh-congCtx-↑ refl σ=σ' = coh↑ σ σ' A (≅-to-≡ σ=σ')

-- -- Coherence property for the term substitution
module _ {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A : Ty Δ i} {t : Tm Δ A} where
  coh[]t
    : σ ≡ τ
    → [ σ ]t t ≅ [ τ ]t t
  coh[]t σ=τ = begin
    [ σ ]t  t ≡⟨ []tm≡[]t t σ ⟨
    [ σ ]tm t ≅⟨ hcong (λ σ → [ σ ]tm t) (≡-to-≅ σ=τ) ⟩
    [ τ ]tm t ≡⟨ []tm≡[]t t τ ⟩
    [ τ ]t  t ∎
    where open ≅-Reasoning

  coh[]t'
    : (p : σ ≡ τ)
    → tr (λ γ → Tm Γ ([ γ ] A)) p ([ σ ]t t) ≡ [ τ ]t t
  coh[]t' p = begin
    tr (λ γ → Tm Γ ([ γ ] A)) p ([ σ ]t t)  ≡⟨ cong (tr (λ γ → Tm Γ ([ γ ] A)) p) ([]tm≡[]t t σ) ⟨
    tr (λ γ → Tm Γ ([ γ ] A)) p ([ σ ]tm t) ≡⟨ apd ([_]tm t) p ⟩
    [ τ ]tm t                               ≡⟨ []tm≡[]t t τ ⟩
    [ τ ]t t                                ∎
      where open ≡-Reasoning

module _ {Γ Γ' Δ : Ctx} {σ : Sub Γ Δ} {σ' : Sub Γ' Δ}
  {A : Ty Δ i} (t : Tm Δ A) where

  coh-congCtx-[]t
    : (Γ=Γ' : Γ ≡ Γ')
    → σ ≅ σ'
    → [ σ ]t t ≅ [ σ' ]t t
  coh-congCtx-[]t refl σ=σ' = coh[]t (≅-to-≡ σ=σ')

-- {-
-- -- WRONG! the coherence of _⇈ Ξ is assumed here  
-- module _ {Γ Δ : Ctx} {σ γ : Sub Γ Δ} where
--   open ≅-Reasoning

--   coh[⇈]tm
--     : (Ξ : Tel Δ) 
--     → {B : Ty (Δ ⧺ Ξ) i} {t : Tm (Δ ⧺ Ξ) B}
--     → σ ≡ γ
--     → [ σ ⇈ Ξ ]t t ≅ [ γ ⇈ Ξ ]t t
--   coh[⇈]tm Ξ {B} {t} σ=γ = begin
--     [ σ ⇈ Ξ ]t  t ≅⟨ ≡-to-≅ $ []tm≡[]t t _ ⟨
--     [ σ ⇈ Ξ ]tm t ≅⟨ icong (λ σ → Sub (_ ⧺ [ σ ]l Ξ) (_ ⧺ Ξ)) σ=γ ([_]tm t) (⇈-cong σ=γ Ξ) ⟩
--     [ γ ⇈ Ξ ]tm t ≡⟨ []tm≡[]t t _ ⟩
--     [ γ ⇈ Ξ ]t  t ∎
-- -}

module RewriteRules where
{-
  Agda reports that [idS]l fails the local confluence while declaring [idS]l a rewrite rule:

  > Local confluence check failed: [ idS ]l (Ξ , A) reduces to both
  > Ξ , A and [ idS ]l Ξ , [ idS ⇈ Ξ ] A which are not equal because
  > A != [ idS ⇈ Ξ ] A of type Ty (Ξ.Γ ⧺ Ξ) i
  > when checking confluence of the rewrite rule [idS]l' with
  > SC+U+Pi+Id.QIIRT.Base.[_]l_-clause2

  It can be fixed by declaring idS⇈ a rewrite rule, but idS⇈ cannot be
  declared with [idS]l together: idS⇈ is not well typed without [idS]l being a rewrite rule.

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
  _ : [ idS ]l (Ξ , A) ≡ (Ξ , A)
  _ = refl

  _ : [ σ ⨟ τ ]l (Ξ , A) ≡ [ σ ]l [ τ ]l (Ξ , A)
  _ = refl


coh-[idS⨟]l
  : [ idS ⨟ σ ]l Ξ ≡ [ σ ]l Ξ
coh-[idS⨟]l = refl

coh-idS⨟⇈
  : (idS ⨟ σ) ⇈ Ξ ≡ σ ⇈ Ξ
coh-idS⨟⇈ = idS⨟ _

coh[idS⨟]
  : [ idS ⨟ σ ] A ≡ [ σ ] A
coh[idS⨟] = refl

coh-[⨟idS]l
  : [ σ ⨟ idS ]l Ξ ≡ [ σ ]l Ξ
coh-[⨟idS]l = refl

coh-⨟idS⇈
  : (σ ⨟ idS) ⇈ Ξ ≡ σ ⇈ Ξ
coh-⨟idS⇈ = _ ⨟idS

coh[⨟idS]
  : [ σ ⨟ idS ] A ≡ [ σ ] A
coh[⨟idS] = refl

coh-[⨟-assoc]l
  : [ (σ ⨟ τ) ⨟ γ ]l Ξ ≡ [ σ ⨟ (τ ⨟ γ) ]l Ξ
coh-[⨟-assoc]l = refl

coh-⨟-assoc
  : (σ ⨟ (τ ⨟ γ)) ⇈ Ξ ≡ ((σ ⨟ τ) ⨟ γ) ⇈ Ξ
coh-⨟-assoc = ⨟-assoc

coh[assocS]
  : [ (σ ⨟ τ) ⨟ γ ] A ≡ [ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Γ ([ σ ] A)) where
  open ≅-Reasoning
  coh[π₁,⇈]
    : (Ξ : Tel Δ)
    → [ π₁ (_,_ σ {A} t) ]l Ξ ≡ [ σ ]l Ξ
    → π₁ (_,_ σ {A} t) ⇈ Ξ ≅ σ ⇈ Ξ
    → (B : Ty (Δ ⧺ Ξ) j)
    → [ π₁ (_,_ σ {A} t) ⇈ Ξ ] B ≅ [ σ ⇈ Ξ ] B
  coh[π₁,]l
    : (Ξ : Tel Δ)
    → [ π₁ (_,_ σ {A} t) ]l Ξ ≡ [ σ ]l Ξ
  coh⇈π₁,
    : (Ξ : Tel Δ)
    → π₁ (_,_ σ {A} t) ⇈ Ξ ≅ σ ⇈ Ξ

  coh[π₁,⇈] Ξ eq _   (U i)      = cong-U (hcong (Γ ⧺_) (≡-to-≅ eq))
  coh[π₁,⇈] Ξ eq eq2 (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) eq) El $
    coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2
  coh[π₁,⇈] Ξ eq eq2 (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Lift $
    coh[π₁,⇈] Ξ eq eq2 B
  coh[π₁,⇈] Ξ eq eq2 (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Π
    (coh[π₁,⇈] Ξ eq eq2 B)
    (coh[π₁,⇈] (Ξ , B) (≅-to-≡ (hcong₂ _,_ (≡-to-≅ eq) (coh[π₁,⇈] Ξ eq eq2 B)))
      (coh-congCtx-↑ B (cong (Γ ⧺_) eq) eq2) C)
  coh[π₁,⇈] Ξ eq eq2 (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) eq) Id
    (coh-congCtx-[]t a (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t t (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2)

  coh[π₁,]l ∅       = refl
  coh[π₁,]l (Ξ , A) = ≅-to-≡ (hcong₂ _,_ (≡-to-≅ $ coh[π₁,]l Ξ) (coh[π₁,⇈] Ξ (coh[π₁,]l Ξ) (coh⇈π₁, Ξ) A))

  coh⇈π₁,   ∅       = ≡-to-≅ π₁,
  coh⇈π₁,   (Ξ , A) = begin
    π₁ (σ , t) ⇈ Ξ ↑ A ≡⟨ ↑=⁺ A (π₁ (σ , t) ⇈ Ξ) ⟩
    (π₁ (σ , t) ⇈ Ξ) ⁺ ≅⟨ icong (λ Ξ' → Sub (Γ ⧺ Ξ') (Δ ⧺ Ξ)) (coh[π₁,]l Ξ) (λ σ → (_⁺ σ {A})) (coh⇈π₁, Ξ) ⟩
    (σ ⇈ Ξ) ⁺          ≡⟨ ↑=⁺ A (σ ⇈ Ξ) ⟨
    σ ⇈ Ξ ↑ A          ∎

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) {i : ℕ} (A : Ty Θ i) (t : Tm Δ ([ τ ] A)) where
  open ≅-Reasoning
  coh[⨟,]'
    : (Ξ : Tel (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≡ [ σ ⨟ τ , [ σ ]tm t ]l Ξ
    →  (σ ⨟ (τ , t)) ⇈ Ξ ≅  (σ ⨟ τ , [ σ ]tm t) ⇈ Ξ
    → (B : Ty ((Θ , A) ⧺ Ξ) j)
    → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ] B

  coh[⨟,]l
    : (Ξ : Tel (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≡ [ σ ⨟ τ , [ σ ]tm t ]l Ξ

  coh⇈⨟,
    : (Ξ : Tel (Θ , A))
    → (σ ⨟ (τ , t)) ⇈ Ξ ≅ (σ ⨟ τ , [ σ ]tm t) ⇈ Ξ

  coh[⨟,]' Ξ eq eq2 (U j)      = cong-U (hcong (Γ ⧺_) (≡-to-≅ eq))
  coh[⨟,]' Ξ eq eq2 (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) eq) El $
    coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2
  coh[⨟,]' Ξ eq eq2 (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Lift $
    coh[⨟,]' Ξ eq eq2 B
  coh[⨟,]' Ξ eq eq2 (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Π
    (coh[⨟,]' Ξ eq eq2 B)
    (coh[⨟,]' (Ξ , B) (≅-to-≡ (hcong₂ _,_ (≡-to-≅ eq) (coh[⨟,]' Ξ eq eq2 B)))
      (coh-congCtx-↑ B (cong (Γ ⧺_) eq) eq2) C)
  coh[⨟,]' Ξ eq eq2 (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) eq) Id
    (coh-congCtx-[]t a (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t t (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2)

  coh[⨟,]l ∅       = refl
  coh[⨟,]l (Ξ , A) = ≅-to-≡ (hcong₂ _,_ (≡-to-≅ $ coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) (coh⇈⨟, Ξ) A))

  coh⇈⨟, ∅       = ≡-to-≅ ⨟,
  coh⇈⨟, (Ξ , A) = begin
    (σ ⨟ (τ , t)) ⇈ Ξ ↑ A             ≡⟨ ↑=⁺ A ((σ ⨟ (τ , t)) ⇈ Ξ) ⟩
    (σ ⨟ (τ , t)) ⇈ Ξ ⁺               ≅⟨ icong (λ Ξ' → Sub (Γ ⧺ Ξ') (_ ⧺ Ξ)) (coh[⨟,]l Ξ) (λ σ → (_⁺ σ {A})) (coh⇈⨟, Ξ) ⟩
    ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ⁺       ≡⟨ ↑=⁺ A (((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ) ⟨
    ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ↑ A     ∎

  coh[⨟,]
    : (Ξ : Tel (Θ , A))
    → (B : Ty ((Θ , A) ⧺ Ξ) j)
    → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ] B
  coh[⨟,] Ξ B = coh[⨟,]' Ξ (coh[⨟,]l Ξ) (coh⇈⨟, Ξ) B

module _ (σ : Sub Γ ∅) where
  open ≅-Reasoning
  coh[η∅]'
    : (Ξ : Tel ∅)
    → [ σ ]l Ξ ≡ [ ∅ ]l Ξ
    →  (σ) ⇈ Ξ ≅  ∅ {Γ} ⇈ Ξ
    → (B : Ty (∅ ⧺ Ξ) j)
    → [ (σ) ⇈ Ξ ] B ≅ [ ∅ {Γ} ⇈ Ξ ] B

  coh[η∅]l
    : (Ξ : Tel ∅)
    → [ σ ]l Ξ ≡ [ ∅ ]l Ξ

  coh⇈η∅
    : (Ξ : Tel ∅)
    → (σ) ⇈ Ξ ≅ ∅ {Γ} ⇈ Ξ

  coh[η∅]' Ξ eq eq2 (U j)      = cong-U (hcong (Γ ⧺_) (≡-to-≅ eq))
  coh[η∅]' Ξ eq eq2 (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) eq) El $
    coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2
  coh[η∅]' Ξ eq eq2 (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Lift $
    coh[η∅]' Ξ eq eq2 B
  coh[η∅]' Ξ eq eq2 (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Π
    (coh[η∅]' Ξ eq eq2 B)
    (coh[η∅]' (Ξ , B) (≅-to-≡ (hcong₂ _,_ (≡-to-≅ eq) (coh[η∅]' Ξ eq eq2 B)))
      (coh-congCtx-↑ B (cong (Γ ⧺_) eq) eq2) C)
  coh[η∅]' Ξ eq eq2 (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) eq) Id
    (coh-congCtx-[]t a (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t t (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2)

  coh[η∅]l ∅       = refl
  coh[η∅]l (Ξ , A) = ≅-to-≡ (hcong₂ _,_ (≡-to-≅ $ coh[η∅]l Ξ) (coh[η∅]' Ξ (coh[η∅]l Ξ) (coh⇈η∅ Ξ) A))

  coh⇈η∅ ∅       = ≡-to-≅ η∅
  coh⇈η∅ (Ξ , A) = begin
    σ ⇈ Ξ ↑ A     ≡⟨ ↑=⁺ A ((σ) ⇈ Ξ) ⟩
    σ ⇈ Ξ ⁺       ≅⟨ icong (λ Ξ' → Sub (Γ ⧺ Ξ') (_ ⧺ Ξ)) (coh[η∅]l Ξ) (λ σ → (_⁺ σ {A})) (coh⇈η∅ Ξ) ⟩
    ∅ {Γ} ⇈ Ξ ⁺       ≡⟨ ↑=⁺ A (∅ {Γ} ⇈ Ξ) ⟨
    ∅ {Γ} ⇈ Ξ ↑ A     ∎

  coh[η∅]
    : (Ξ : Tel ∅)
    → (B : Ty (∅ ⧺ Ξ) j)
    → [ σ ⇈ Ξ ] B ≅ [ ∅ {Γ} ⇈ Ξ ] B
  coh[η∅] Ξ B = coh[η∅]' Ξ (coh[η∅]l Ξ) (coh⇈η∅ Ξ) B

module _ (σ : Sub Γ (Δ , A)) where
  open ≅-Reasoning
  coh[η,]'
    : (Ξ : Tel (Δ , A))
    → [ σ ]l Ξ ≡ [ π₁ σ , π₂ σ ]l Ξ
    →  σ ⇈ Ξ ≅  (π₁ σ , π₂ σ) ⇈ Ξ
    → (B : Ty ((Δ , A) ⧺ Ξ) j)
    → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B

  coh[η,]l
    : (Ξ : Tel (Δ , A))
    → [ σ ]l Ξ ≡ [ π₁ σ , π₂ σ ]l Ξ

  coh⇈η,
    : (Ξ : Tel (Δ , A))
    → σ ⇈ Ξ ≅ (π₁ σ , π₂ σ) ⇈ Ξ

  coh[η,]' Ξ eq eq2 (U j)      = cong-U (hcong (Γ ⧺_) (≡-to-≅ eq))
  coh[η,]' Ξ eq eq2 (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) eq) El $
    coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2
  coh[η,]' Ξ eq eq2 (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Lift $
    coh[η,]' Ξ eq eq2 B
  coh[η,]' Ξ eq eq2 (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) eq) Π
    (coh[η,]' Ξ eq eq2 B)
    (coh[η,]' (Ξ , B) (≅-to-≡ (hcong₂ _,_ (≡-to-≅ eq) (coh[η,]' Ξ eq eq2 B)))
      (coh-congCtx-↑ B (cong (Γ ⧺_) eq) eq2) C)
  coh[η,]' Ξ eq eq2 (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) eq) Id
    (coh-congCtx-[]t a (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t t (cong (Γ ⧺_) eq) eq2)
    (coh-congCtx-[]t u (cong (Γ ⧺_) eq) eq2)

  coh[η,]l ∅       = refl
  coh[η,]l (Ξ , A) = ≅-to-≡ (hcong₂ _,_ (≡-to-≅ $ coh[η,]l Ξ) (coh[η,]' Ξ (coh[η,]l Ξ) (coh⇈η, Ξ) A))

  coh⇈η, ∅       = ≡-to-≅ η,
  coh⇈η, (Ξ , A) = begin
    σ ⇈ Ξ ↑ A     ≡⟨ ↑=⁺ A (σ ⇈ Ξ) ⟩
    σ ⇈ Ξ ⁺       ≅⟨ icong (λ Ξ' → Sub (Γ ⧺ Ξ') (_ ⧺ Ξ)) (coh[η,]l Ξ) (λ σ → (_⁺ σ {A})) (coh⇈η, Ξ) ⟩
    (π₁ σ , π₂ σ) ⇈ Ξ ⁺       ≡⟨ ↑=⁺ A ((π₁ σ , π₂ σ) ⇈ Ξ) ⟨
    (π₁ σ , π₂ σ) ⇈ Ξ ↑ A     ∎

  coh[η,]
    : (Ξ : Tel (Δ , A))
    → (B : Ty ((Δ , A) ⧺ Ξ) j)
    → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B
  coh[η,] Ξ B = coh[η,]' Ξ (coh[η,]l Ξ) (coh⇈η, Ξ) B
