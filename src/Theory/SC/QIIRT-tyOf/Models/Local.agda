open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Models.Local
  (A : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (SCᵐ : SCᴹ A)
  (Ctxᴬ-is-set : isSet (A .Motive.Ctxᴬ))
  (Tmᴬ-is-set : {Γᴹ : A .Motive.Ctxᴬ} → isSet (A .Motive.Tmᴬ Γᴹ)) where

open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.HITs.SetQuotients
  renaming (elim to elim/; rec to rec/)
open import Cubical.Relation.Binary.Base

open Motive A
open SCᴹ SCᵐ

cong,∶[]
  : {σᴹ σ'ᴹ : Subᴬ Γᴹ Δᴹ}{tᴹ t'ᴹ : Tmᴬ Γᴹ}
  → (pᴹ : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ) (p'ᴹ : tyOfᴬ t'ᴹ ≡ Aᴹ [ σ'ᴹ ]Tᴹ)
  → σᴹ ≡ σ'ᴹ → tᴹ ≡ t'ᴹ
  → (σᴹ ,ᴹ tᴹ ∶[ pᴹ ]) ≡ (σ'ᴹ ,ᴹ t'ᴹ ∶[ p'ᴹ ])
cong,∶[] {Aᴹ = Aᴹ} p p' eqσ eqt =
  cong₃ _,ᴹ_∶[_] eqσ eqt (isSet→SquareP (λ _ _ → Tyᴬ-is-set) p p' (cong tyOfᴬ eqt) (cong (Aᴹ [_]Tᴹ) eqσ))

ℓ! = ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record Ty³ (Γᴹ : Ctxᴬ) : Set ℓ! where
  constructor ty³
  field
    V : Ctxᴬ
    E : Tyᴬ V
    ⌜_⌝ : Subᴬ Γᴹ V
  [_]³ : Tyᴬ Γᴹ
  [_]³ = E [ ⌜_⌝ ]Tᴹ
open Ty³

Ty³-is-set : isSet (Ty³ Γᴹ)
Ty³-is-set {Γᴹ} A³ A'³ p q i j = record
  { V = isSet→SquareP (λ _ _ → Ctxᴬ-is-set) refl refl (cong V p) (cong V q) j i
  ; E = isSet→SquareP (λ j i → Tyᴬ-is-set {isSet→SquareP (λ _ _ → Ctxᴬ-is-set) refl refl (cong V p) (cong V q) j i})
                       refl refl (cong E p) (cong E q) j i
  ; ⌜_⌝ = isSet→SquareP (λ j i → Subᴬ-is-set {Γᴹ} {isSet→SquareP (λ _ _ → Ctxᴬ-is-set) refl refl (cong V p) (cong V q) j i})
                         refl refl (cong ⌜_⌝ p) (cong ⌜_⌝ q) j i
  }

_≡³_ : Ty³ Γᴹ → Ty³ Γᴹ → Set ℓ₂
A³ ≡³ A'³ = [ A³ ]³ ≡ [ A'³ ]³

open BinaryRelation
≡³-is-equiv : isEquivRel {A = Ty³ Γᴹ} _≡³_
≡³-is-equiv = record
  { reflexive = λ _ → refl
  ; symmetric = λ _ _ → sym
  ; transitive = λ _ _ _ → _∙_
  }

≡³-is-propvalued : isPropValued {A = Ty³ Γᴹ} _≡³_
≡³-is-propvalued A³ A'³ = Tyᴬ-is-set [ A³ ]³ [ A'³ ]³

Ty! : Ctxᴬ → Set ℓ!
Ty! Γᴹ = Ty³ Γᴹ / _≡³_

pattern ty! A³ = [ A³ ]
pattern []³≡ p i = eq/ _ _ p i

[_]! : Ty! Γᴹ → Tyᴬ Γᴹ
[_]! = rec/ Tyᴬ-is-set [_]³ λ _ _ p → p

pattern !-syntax Eᴹ σᴹ = ty! (ty³ _ Eᴹ σᴹ)
syntax !-syntax Eᴹ σᴹ = ⟨ Eᴹ , σᴹ ⟩!

eff! : {A³ A'³ : Ty³ Γᴹ} → _≡_ {A = Ty! Γᴹ} (ty! A³) (ty! A'³) → A³ ≡³ A'³
eff! = effective ≡³-is-propvalued ≡³-is-equiv _ _

Ty!-is-set : isSet (Ty! Γᴹ)
Ty!-is-set = squash/

tyOf! : Tmᴬ Γᴹ → Ty! Γᴹ
tyOf! tᴹ = ty! (ty³ _ (tyOfᴬ tᴹ) idSᴹ)

_[_]T! : Ty! Δᴹ → (σᴹ : Subᴬ Γᴹ Δᴹ) → Ty! Γᴹ
A! [ σᴹ ]T! =
  rec/ Ty!-is-set
       (λ A³ → ⟨ E A³ , ⌜ A³ ⌝ ∘ᴹ σᴹ ⟩!)
       (λ _ _ p → []³≡ (sym ([∘]Tᴹ _ _ _) ∙ cong (_[ σᴹ ]Tᴹ) p ∙ [∘]Tᴹ _ _ _))
       A!

tyOf!π₂ᴹ
  : {A! : Ty! Δᴹ} (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ [ A! ]!))
  → tyOf! (π₂ᴹ {Aᴹ = [ A! ]!} σᴹ) ≡ A! [ π₁ᴹ σᴹ ]T!
tyOf!π₂ᴹ {Δᴹ} {Γᴹ} { A! } =
  elimProp {P = λ A! → (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ [ A! ]!)) → tyOf! (π₂ᴹ σᴹ) ≡ A! [ π₁ᴹ σᴹ ]T! }
    (λ _ → isPropΠ λ _ → squash/ _ _)
    (λ A³ σᴹ → eq/ _ _ (sym [idS]Tᴹ ∙ tyOfπ₂ᴹ σᴹ ∙ [∘]Tᴹ _ _ _))
    A!

_,ᴹ!_∶[_]
  : ∀{ A! } → (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) → tyOf! tᴹ ≡ A! [ σᴹ ]T!
  → Subᴬ Γᴹ (Δᴹ ,ᴹ [ A! ]!)
_,ᴹ!_∶[_] {Γᴹ} {Δᴹ} {A!} σᴹ tᴹ =
  elim/ {P = λ Aᴹ → tyOf! tᴹ ≡ Aᴹ [ σᴹ ]T! → Subᴬ Γᴹ (Δᴹ ,ᴹ [ Aᴹ ]!)}
    (λ _ → isSet→ Subᴬ-is-set)
    (λ A³ p → σᴹ ,ᴹ tᴹ ∶[ [idS]Tᴹ ∙ eff! p ∙ sym ([∘]Tᴹ _ _ _) ])
    (λ A³ A'³ q i p → σᴹ ,ᴹ tᴹ ∶[
      (λ j → isSet→SquareP (λ _ _ → Tyᴬ-is-set)
        refl
        (λ i → [ eq/ A³ A'³ q i ]! [ σᴹ ]Tᴹ)
        ([idS]Tᴹ ∙ eff! (transp (λ j → tyOf! tᴹ ≡ eq/ A³ A'³ q (i ∧ ~ j) [ σᴹ ]T!) (~ i) p) ∙ sym ([∘]Tᴹ _ _ _))
        ([idS]Tᴹ ∙ eff! (transp (λ j → tyOf! tᴹ ≡ eq/ A³ A'³ q (i ∨ j) [ σᴹ ]T!) i p) ∙ sym ([∘]Tᴹ _ _ _))
        j i)
    ])
    A!

SC!ᵃ : Motive _ _ _ _
SC!ᵃ .Motive.Ctxᴬ       = Ctxᴬ
SC!ᵃ .Motive.Tyᴬ        = Ty!
SC!ᵃ .Motive.Subᴬ       = Subᴬ
SC!ᵃ .Motive.Tmᴬ        = Tmᴬ
SC!ᵃ .Motive.tyOfᴬ      = tyOf!
SC!ᵃ .Motive.Tyᴬ-is-set = Ty!-is-set
SC!ᵃ .Motive.Subᴬ-is-set = Subᴬ-is-set

SC!ᵐ : SCᴹ SC!ᵃ
SC!ᵐ .SCᴹ.∅ᴹ = ∅ᴹ
SC!ᵐ .SCᴹ._,ᴹ_ Γᴹ A! = Γᴹ ,ᴹ [ A! ]!
SC!ᵐ .SCᴹ._[_]Tᴹ = _[_]T!
SC!ᵐ .SCᴹ._[_]tᴹ = _[_]tᴹ
SC!ᵐ .SCᴹ.tyOf[]ᴹ {tᴹ = tᴹ} {σᴹ = σᴹ} =
  []³≡ (cong (_[ idSᴹ ]Tᴹ) tyOf[]ᴹ 
       ∙ [∘]Tᴹ _ _ _
       ∙ cong (tyOfᴬ tᴹ [_]Tᴹ) ((σᴹ ∘idSᴹ)
       ∙ sym (idS∘ᴹ σᴹ)))
  -- [WARN]: equality should be on Tyᴬ
SC!ᵐ .SCᴹ.∅Sᴹ = ∅Sᴹ
SC!ᵐ .SCᴹ._,ᴹ_∶[_] {_} {_} {Aᴹ} = _,ᴹ!_∶[_] {A! = Aᴹ}
SC!ᵐ .SCᴹ.idSᴹ = idSᴹ
SC!ᵐ .SCᴹ._∘ᴹ_ = _∘ᴹ_
SC!ᵐ .SCᴹ.π₁ᴹ = π₁ᴹ
SC!ᵐ .SCᴹ.π₂ᴹ = π₂ᴹ
SC!ᵐ .SCᴹ.tyOfπ₂ᴹ {_} {_} {Aᴹ} = tyOf!π₂ᴹ {A! = Aᴹ}
  -- [WARN]: equality should be on Tyᴬ
SC!ᵐ .SCᴹ.idS∘ᴹ_ = idS∘ᴹ_
SC!ᵐ .SCᴹ._∘idSᴹ = _∘idSᴹ
SC!ᵐ .SCᴹ.assocSᴹ = assocSᴹ
SC!ᵐ .SCᴹ.[idS]Tᴹ {Γᴹ} {Aᴹ} =
  elimProp {P = λ A! → A! ≡ A! [ idSᴹ ]T! }
    (λ _ → squash/ _ _)
    (λ A³ → eq/ _ _ ([idS]Tᴹ ∙ [∘]Tᴹ _ _ _))
    Aᴹ
SC!ᵐ .SCᴹ.[∘]Tᴹ {Θᴹ} {Γᴹ} {Δᴹ} = 
  elimProp {P = λ Aᴹ → (σᴹ : Subᴬ Γᴹ Δᴹ)(τᴹ : Subᴬ Δᴹ Θᴹ) → ((Aᴹ [ τᴹ ]T!) [ σᴹ ]T!) ≡ (Aᴹ [ τᴹ ∘ᴹ σᴹ ]T!)}
    (λ _ → isPropΠ λ _ → isPropΠ λ _ → squash/ _ _)
    λ A³ σᴹ τᴹ i → ⟨ E A³ , assocSᴹ σᴹ τᴹ ⌜ A³ ⌝ i ⟩!
SC!ᵐ .SCᴹ.,∘ᴹ {Δᴹ} {Θᴹ} {Γᴹ} {Aᴹ} σᴹ tᴹ τᴹ =
  elimProp {P = λ A!
    → (p : tyOf! tᴹ ≡ (A! [ σᴹ ]T!))(q : tyOf! (tᴹ [ τᴹ ]tᴹ) ≡ (A! [ σᴹ ∘ᴹ τᴹ ]T!)) → (_,ᴹ!_∶[_] {A! = A!} σᴹ tᴹ p) ∘ᴹ τᴹ ≡ _}
      -- _,ᴹ!_∶[_] { A! = A! } (σᴹ ∘ᴹ τᴹ) (tᴹ [ τᴹ ]tᴹ) q
      -- [WARN]: Fill in this implicit argument takes much more time to type check
    (λ A! → isPropΠ λ p → isPropΠ λ q → Subᴬ-is-set _ _)
    (λ A³ p q → ,∘ᴹ σᴹ tᴹ τᴹ _ _)
    Aᴹ
SC!ᵐ .SCᴹ.ηπᴹ {Γᴹ} {Δᴹ} {Aᴹ} =
  elimProp {P = λ A! → (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ [ A! ]!)) → σᴹ ≡ _}
    -- _,ᴹ!_∶[_] {Γᴹ} {Δᴹ} {A!} (π₁ᴹ σᴹ) (π₂ᴹ σᴹ) (tyOf!π₂ᴹ σᴹ)
    -- [WARN]: Fill in this implicit argument takes much more time to type check
    (λ _ → isPropΠ λ σᴹ → Subᴬ-is-set σᴹ _)
    (λ A³ σᴹ → ηπᴹ σᴹ ∙ cong,∶[] _ _ refl refl)
    Aᴹ
SC!ᵐ .SCᴹ.η∅ᴹ = η∅ᴹ
SC!ᵐ .SCᴹ.βπ₁ᴹ {Aᴹ = Aᴹ} σᴹ tᴹ = 
  elimProp {P = λ A! → (p : tyOf! tᴹ ≡ (A! [ σᴹ ]T!)) → π₁ᴹ (_,ᴹ!_∶[_] {A! = A!} σᴹ tᴹ p) ≡ σᴹ}
    (λ _ → isPropΠ λ _ → Subᴬ-is-set _ σᴹ)
    (λ A³ p → βπ₁ᴹ σᴹ tᴹ _)
    Aᴹ
SC!ᵐ .SCᴹ.βπ₂ᴹ {Aᴹ = Aᴹ} σᴹ tᴹ =
  elimProp {P = λ A! → (p : tyOf! tᴹ ≡ (A! [ σᴹ ]T!)) → π₂ᴹ (_,ᴹ!_∶[_] {A! = A!} σᴹ tᴹ p) ≡ tᴹ}
    (λ _ → isPropΠ λ _ → Tmᴬ-is-set _ tᴹ)
    (λ A³ p → βπ₂ᴹ σᴹ tᴹ _)
    Aᴹ
SC!ᵐ .SCᴹ.[idS]tᴹ = [idS]tᴹ
SC!ᵐ .SCᴹ.[∘]tᴹ = [∘]tᴹ
SC!ᵐ .SCᴹ.Uᴹ = ⟨ Uᴹ , idSᴹ ⟩!
SC!ᵐ .SCᴹ.U[]ᴹ {σᴹ = σᴹ} = []³≡ (U[]ᴹ {σᴹ = idSᴹ ∘ᴹ σᴹ} ∙ sym (U[]ᴹ {σᴹ = idSᴹ}))
  -- [WARN]: equality should be on Tyᴬ