open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient
  (C : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄)  where

open SC C
open GVars

ℓ! = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃

record Ty³ (Γ : Ctx) : Set ℓ! where
  inductive
  eta-equality
  constructor ⟨_,_⟩!
  field
    {V} : Ctx
    E   : Ty V
    ⌜_⌝ : Sub Γ V

  [_]³ : Ty Γ
  [_]³ = E [ ⌜_⌝ ]T
open Ty³

ty³ : (V : Ctx) → Ty V → Sub Γ V → Ty³ Γ
ty³ V E σ = ⟨ E , σ ⟩!

-- Ty³-is-set : isSet (Ty³ Γ)
-- Ty³-is-set {Γ} A³ A'³ p q i j = record
--   { V = isSet→SquareP (λ _ _ → Ctxᴬ-is-set) refl refl (cong V p) (cong V q) j i
--   ; E = isSet→SquareP (λ j i → Tyᴬ-is-set {isSet→SquareP (λ _ _ → Ctxᴬ-is-set) refl refl (cong V p) (cong V q) j i})
--                        refl refl (cong E p) (cong E q) j i
--   ; ⌜_⌝ = isSet→SquareP (λ j i → Subᴬ-is-set {Γ} {isSet→SquareP (λ _ _ → Ctxᴬ-is-set) refl refl (cong V p) (cong V q) j i})
--                          refl refl (cong ⌜_⌝ p) (cong ⌜_⌝ q) j i
--   }

Tm! : Ctx → Set _
Tm! Γ = Σ[ T ∈ Ty³ Γ ] Σ[ t ∈ (Tm Γ) ] tyOf t ≡ [ T ]³

Tm!-≡ : {Γ : Ctx} → {u t : Tm! Γ}
      → fst u ≡ fst t → fst (snd u) ≡ fst (snd t) → u ≡ t
Tm!-≡ {Γ} {A , u , p} {B , t , q} r w i =
 r i ,
 w i ,
 isProp→PathP {B = λ j → tyOf (w j) ≡ [ r j ]³} (λ j → UIP) p q i
-- isProp→PathP {B = λ j → tyOf (w j) ≡ [ r j ]³} (λ j → Ty-is-set (tyOf (w j)) [ r j ]³) p q i

tyOf! : Tm! Γ → Ty³ Γ
tyOf! = fst

_[_]T! : Ty³ Δ → (σ : Sub Γ Δ) → Ty³ Γ
A! [ σ ]T! = ⟨ E A! , ⌜ A! ⌝ ∘ σ ⟩!

_[_]t! : Tm! Δ → (σ : Sub Γ Δ) → Tm! Γ
(T , t , p) [ σ ]t! =
 (T [ σ ]T!) ,
 (t [ σ ]t) ,
 tyOf[] ∙ cong _[ σ ]T p ∙ [∘]T (E T) σ ⌜ T ⌝

_,!_ : (Γ : Ctx) → Ty³ Γ → Ctx
Γ ,! A! = Γ ,C [ A! ]³

_,!_∶[_] : {A : Ty³ Δ} (σ : Sub Γ Δ) (t : Tm! Γ) → tyOf! t ≡ A [ σ ]T!
        → Sub Γ (Δ ,! A)
_,!_∶[_] {A = A} σ (B , t , q) p = σ , t ∶[ q ∙ cong [_]³ p ∙ sym ([∘]T (E A) σ ⌜ A ⌝) ]

!C : Motive
!C .Motive.Ctx        = Ctx
!C .Motive.Ty         = Ty³
!C .Motive.Sub        = Sub
!C .Motive.Tm         = Tm!
!C .Motive.tyOf       = tyOf!
-- SC!ᵃ .Motive.Ty-is-set  = Ty³-is-set
-- SC!ᵃ .Motive.Sub-is-set = Sub-is-set
-- SC!ᵃ .Motive.Tm-is-set  = isSetΣ Ty³-is-set λ _ → isSetΣ Tm-is-set λ _ → isProp→isSet (Ty-is-set _ _)

!SC : IsSC !C
!SC .IsSC.∅ = ∅
!SC .IsSC._,C_ = _,!_
!SC .IsSC._[_]T = _[_]T!
!SC .IsSC._[_]t = _[_]t!
!SC .IsSC.tyOf[] = refl
!SC .IsSC.∅S = ∅S
!SC .IsSC._,_∶[_] = _,!_∶[_]
!SC .IsSC.idS = idS
!SC .IsSC._∘_ = _∘_
!SC .IsSC.π₁ = π₁
!SC .IsSC.π₂ {A = A} σ =
  (A [ π₁ σ ]T!) , π₂ σ , tyOfπ₂ σ ∙ [∘]T (E A) (π₁ σ) ⌜ A ⌝
!SC .IsSC.tyOfπ₂ σ = refl
!SC .IsSC.idS∘_ = idS∘_
!SC .IsSC._∘idS = _∘idS
!SC .IsSC.assocS = assocS
!SC .IsSC.[idS]T {Γ} {A} =
  cong (ty³ (A .V) (E A)) (sym (⌜ A ⌝ ∘idS))
!SC .IsSC.[∘]T A σ τ =
  cong (ty³ (A .V) (E A)) (assocS σ τ ⌜ A ⌝)
!SC .IsSC.,∘ {A = A} σ (B , t , r) τ p q = ,∘ σ t τ _ _
!SC .IsSC.ηπ σ = ηπ σ ∙ cong,∶[] _ _ refl refl
!SC .IsSC.η∅ = η∅
!SC .IsSC.βπ₁ σ (B , t , q) p =  βπ₁ σ t _
!SC .IsSC.βπ₂ {A = A} σ (B , t , q) p =
  Tm!-≡ (cong (A [_]T!) (βπ₁ σ t _) ∙ sym p) (βπ₂ σ t _)
!SC .IsSC.[idS]t (B , t , q) = Tm!-≡ (!SC .IsSC.[idS]T) ([idS]t t)
!SC .IsSC.[∘]t (B , t , q) σ τ =
  Tm!-≡ (!SC .IsSC.[∘]T B σ τ) ([∘]t t σ τ)
!SC .IsSC.U = ⟨ U , ∅S ⟩!
!SC .IsSC.U[] {σ = σ} = cong (ty³ ∅ U) (η∅ (∅S ∘ σ))

_! : SC _ _ _ _
_! = record { mot = !C ; isSC = !SC }
