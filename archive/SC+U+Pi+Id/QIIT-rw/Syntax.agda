module SC+U+Pi+Id.QIIT-rw.Syntax where
 
open import Prelude

infixr 15 [_]_ [_]tm_
infixl 10 _⨟_
infixl 4 _,ᶜ_ _,ˢ_

variable
  i j k : ℕ

postulate
  Ctx :                      Set
  Ty  : (Γ : Ctx) → ℕ      → Set
  Sub : (Γ : Ctx) → Ctx    → Set
  Tm  : (Γ : Ctx) → Ty Γ i → Set

  ∅ᶜ
    : Ctx
  _,ᶜ_
    : ∀{i}
    → (Γ : Ctx) (A : Ty Γ i)
    → Ctx
  [_]_
    : ∀{Γ Δ}
    → (σ : Sub Γ Δ) (A : Ty Δ i)
    → Ty Γ i
  ∅ˢ
    : ∀{Γ} → Sub Γ ∅ᶜ
  _,ˢ_
    : ∀{Γ Δ}
    → (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Γ ([ σ ] A))
    → Sub Γ (Δ ,ᶜ A) 
  idS
    : ∀{Γ} → Sub Γ Γ
  _⨟_
    : ∀{Γ Δ Θ}
    → (σ : Sub Γ Δ) (τ : Sub Δ Θ) 
    → Sub Γ Θ
  π₁
    : ∀{Γ Δ} {A : Ty Δ i}
    → Sub Γ (Δ ,ᶜ A)
    → Sub Γ Δ

  [idS]   : ∀{Γ} {A : Ty Γ i} → [ idS {Γ} ] A ≡ A
  [⨟]     : ∀{Γ Δ Θ} {σ : Sub Γ Δ} {τ : Sub Δ Θ} {A : Ty Θ i}
          → [ σ ⨟ τ      ] A ≡ [ σ ] [ τ ] A

  U
    : ∀{Γ}
    → (i : ℕ)
    → Ty Γ (suc i)
  El
    : ∀{Γ}
    → Tm Γ (U i) 
    → Ty Γ i
  Lift
    : ∀{Γ}
    → Ty Γ i
    → Ty Γ (suc i)
  Π
    : ∀{Γ}
    → (A : Ty Γ i) (B : Ty (Γ ,ᶜ A) i)
    → Ty Γ i
  Id
    : ∀{Γ}
    → (a : Tm Γ (U i)) (t u : Tm Γ (El a)) 
    → Ty Γ i
  π₂
    : ∀{Γ Δ} {A : Ty Δ i}
    → (σ : Sub Γ (Δ ,ᶜ A))
    → Tm Γ ([ π₁ σ ] A)
  [_]tm_
    : ∀{Γ Δ}
    → (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Δ A)
    → Tm Γ ([ σ ] A)
  c
    : ∀{Γ}
    → Ty Γ i
    → Tm Γ (U i)
  mk
    : ∀{Γ} {A : Ty Γ i}
    → Tm Γ A
    → Tm Γ (Lift A)
  un
    : ∀{Γ} {A : Ty Γ i}
    → Tm Γ (Lift A)
    → Tm Γ A
  ƛ_
    : ∀{Γ} {A : Ty Γ i} {B : Ty (Γ ,ᶜ A) i}
    → Tm (Γ ,ᶜ A) B
    → Tm Γ (Π A B)
  app
    : ∀{Γ} {A : Ty Γ i} {B : Ty (Γ ,ᶜ A) i}
    → Tm Γ (Π A B) 
    → Tm (Γ ,ᶜ A) B
  refl'
    : ∀{Γ} {a : Tm Γ (U i)} (t : Tm Γ (El a))
    → Tm Γ (Id a t t)


_↑_ : ∀{Γ Δ} (σ : Sub Γ Δ) (A : Ty Δ i) → Sub (Γ ,ᶜ [ σ ] A) (Δ ,ᶜ A)
σ ↑ A = π₁ idS ⨟ σ ,ˢ tr (Tm _) (sym [⨟]) (π₂ idS)

variable
  Γ Δ Θ : Ctx
  A B C : Ty Γ i
  σ τ γ : Sub Γ Δ
  t u v : Tm Γ A

postulate
-- Equality constructors for substitutions
  _⨟idS
    : (σ : Sub Γ Δ)
    → σ ⨟ idS ≡ σ
  idS⨟_
    : (σ : Sub Γ Δ)
    → idS ⨟ σ ≡ σ
  ⨟-assoc
    : σ ⨟ (τ ⨟ γ) ≡ (σ ⨟ τ) ⨟ γ
  π₁,
    : π₁ (σ ,ˢ t) ≡ σ
  ⨟,
    : (σ ⨟ (τ ,ˢ t)) ≡ (σ ⨟ τ ,ˢ tr (Tm _) (sym [⨟]) ([ σ ]tm t))
  η∅
    : (σ : Sub Γ ∅ᶜ)
    → σ ≡ ∅ˢ
  η,
    : {σ : Sub Γ (Δ ,ᶜ A)}
    → σ ≡ (π₁ σ ,ˢ π₂ σ)
-- Equality constructors for terms
  [idS]tm
    : tr (Tm Γ) [idS] ([ idS ]tm t) ≡ t
  [⨟]tm
    : tr (Tm Γ) [⨟] ([ σ ⨟ τ ]tm t) ≡ [ σ ]tm [ τ ]tm t
  π₂,
    : {σ : Sub Γ Δ}{A : Ty Δ i}{t : Tm Γ ([ σ ] A)}
    →  π₂ (σ ,ˢ t) ≡ tr (λ σ → Tm Γ ([ σ ] A)) (sym π₁,) t

-- Structural rules for type formers
  []U
    : [ σ ] (U i) ≡ U i
  []El
    : (σ : Sub Γ Δ) (u : Tm Δ (U i))
    → [ σ ] (El u) ≡ El (tr (Tm Γ) []U ([ σ ]tm u))
  []Lift
    : [ σ ] (Lift A) ≡ Lift ([ σ ] A)
  []Π
    : [ σ ] Π A B ≡ Π ([ σ ] A) ([ σ ↑ A ] B)
  []Id
    : {σ : Sub Γ Δ} {a : Tm Δ (U i)} {t u : Tm Δ (El a)}
    → [ σ ] (Id a t u)
    ≡ Id (tr (Tm Γ) []U ([ σ ]tm a))
      (tr (Tm Γ) ([]El σ a) ([ σ ]tm t))
      (tr (Tm Γ) ([]El σ a) ([ σ ]tm u))

-- Structural rules for term formers
  []tc
    : (σ : Sub Γ Δ) (A : Ty Δ i)
    → tr (Tm Γ) []U ([ σ ]tm (c A))
    ≡ c ([ σ ] A)
  []mk
    : (σ : Sub Γ Δ) (t : Tm Δ A)
    → tr (Tm Γ) []Lift ([ σ ]tm (mk t))
    ≡ mk ([ σ ]tm t) -- mk ([ σ ]tm t)
  []un
    : (σ : Sub Γ Δ) (A : Ty Δ i) (t : Tm Δ (Lift A))
    → [ σ ]tm un t ≡ un (tr (Tm Γ) []Lift $ [ σ ]tm t)
  []refl
    : (σ : Sub Γ Δ) {a : Tm Δ (U i)} (t : Tm Δ (El a))
    → tr (Tm Γ) []Id ([ σ ]tm (refl' t))
    ≡ refl' (tr (Tm Γ) ([]El σ a) ([ σ ]tm t))

-- Computational rules
  Uβ
    : El (c A) ≡ A
  Uη
    : c (El u) ≡ u
  Liftβ
    : un (mk u) ≡ u
  Liftη
    : mk (un u) ≡ u
  reflect
    : {a : Tm Γ (U i)} {t u : Tm Γ (El a)} → Tm Γ (Id a t u)
    → t ≡ u
  []ƛ
    : (σ : Sub Γ Δ) (t : Tm (Δ ,ᶜ A) B)
    → tr (Tm Γ) []Π ([ σ ]tm (ƛ t)) ≡ (ƛ ([ σ ↑ A ]tm t))
  Πβ
    : app (ƛ t) ≡ t
  Πη
    : ƛ (app t) ≡ t
-- rewrite equality constructors
{-# REWRITE
  [idS] [⨟] []U []El []Lift []Π []Id
  _⨟idS idS⨟_ ⨟-assoc π₁, π₂, ⨟,
#-}

-- rewrite equality constructors to refl
postulate
  [idS]≡refl : [idS] {A = A}  ≡ refl
  [⨟]≡refl : [⨟] {σ = σ} {τ} {A} ≡ refl
  []U≡refl : []U {σ = σ} {i} ≡ refl
  []El≡refl : []El σ t ≡ refl
  []Lift≡refl : []Lift {σ = σ} {A = A} ≡ refl
  []Π≡refl : []Π {σ = σ} {A = A} {B = B} ≡ refl
  ⨟idS≡refl : σ ⨟idS ≡ refl
  idS⨟≡refl : idS⨟ σ ≡ refl
  ⨟-assoc≡refl : ⨟-assoc {σ = σ} {τ = τ} {γ = γ} ≡ refl
  π₁,≡refl : π₁, {σ = σ} {t = t} ≡ refl
  π₂,≡refl : {t : Tm Γ ([ σ ] A)} → π₂, {σ = σ} {A} {t} ≡ refl
  ⨟,≡refl : ⨟, {σ = σ} {τ = τ} {t = t} ≡ refl

{-# REWRITE
  [idS]≡refl [⨟]≡refl []U≡refl []El≡refl []Lift≡refl []Π≡refl
  ⨟idS≡refl idS⨟≡refl ⨟-assoc≡refl π₁,≡refl π₂,≡refl ⨟,≡refl
#-}
