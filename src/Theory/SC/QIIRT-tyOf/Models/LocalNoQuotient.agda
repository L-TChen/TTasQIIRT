open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient
  (A : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (SCᵐ : SCᴹ A)
  (Ctxᴬ-is-set : isSet (A .Motive.Ctxᴬ)) where

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



pattern !-syntax Eᴹ σᴹ = ty³ _ Eᴹ σᴹ
syntax !-syntax Eᴹ σᴹ = ⟨ Eᴹ , σᴹ ⟩!

Tm! : Ctxᴬ → Set _
Tm! Γᴹ = Σ (Ty³ Γᴹ) (λ T → Σ (Tmᴬ Γᴹ) λ t → tyOfᴬ t ≡ [ T ]³)

Tm!-≡ : {Γᴹ : Ctxᴬ} → {u t : Tm! Γᴹ}
      → fst u ≡ fst t → fst (snd u) ≡ fst (snd t) → u ≡ t
Tm!-≡ {Γᴹ} {Aᴹ , u , p} {Bᴹ , t , q} r w i =
 r i ,
 w i ,
 isProp→PathP {B = λ j → tyOfᴬ (w j) ≡ [ r j ]³} (λ j → Tyᴬ-is-set (tyOfᴬ (w j)) [ r j ]³) p q i

tyOf! : Tm! Γᴹ → Ty³ Γᴹ
tyOf! = fst

_[_]T! : Ty³ Δᴹ → (σᴹ : Subᴬ Γᴹ Δᴹ) → Ty³ Γᴹ
A! [ σᴹ ]T! = ⟨ E A! , ⌜ A! ⌝ ∘ᴹ σᴹ ⟩!

_[_]t! : Tm! Δᴹ → (σᴹ : Subᴬ Γᴹ Δᴹ) → Tm! Γᴹ
(T , t , p) [ σᴹ ]t! =
 (T [ σᴹ ]T!) ,
 (t [ σᴹ ]tᴹ) ,
 tyOf[]ᴹ ∙ cong _[ σᴹ ]Tᴹ p ∙ [∘]Tᴹ (E T) σᴹ ⌜ T ⌝

SC!ᵃ : Motive _ _ _ _
SC!ᵃ .Motive.Ctxᴬ       = Ctxᴬ
SC!ᵃ .Motive.Tyᴬ        = Ty³
SC!ᵃ .Motive.Subᴬ       = Subᴬ
SC!ᵃ .Motive.Tmᴬ        = Tm!
SC!ᵃ .Motive.tyOfᴬ      = tyOf!
SC!ᵃ .Motive.Tyᴬ-is-set = Ty³-is-set
SC!ᵃ .Motive.Subᴬ-is-set = Subᴬ-is-set

SC!ᵐ : SCᴹ SC!ᵃ
SC!ᵐ .SCᴹ.∅ᴹ = ∅ᴹ
SC!ᵐ .SCᴹ._,ᴹ_ Γᴹ A! = Γᴹ ,ᴹ [ A! ]³
SC!ᵐ .SCᴹ._[_]Tᴹ = _[_]T!
SC!ᵐ .SCᴹ._[_]tᴹ = _[_]t!
SC!ᵐ .SCᴹ.tyOf[]ᴹ {tᴹ = tᴹ} {σᴹ = σᴹ} =
  refl
SC!ᵐ .SCᴹ.∅Sᴹ = ∅Sᴹ
SCᴹ._,ᴹ_∶[_] SC!ᵐ {Γᴹ} {Δᴹ} {Aᴹ} σᴹ (Bᴹ , t , q) p =
 σᴹ ,ᴹ t ∶[ q ∙ cong [_]³ p ∙ sym ([∘]Tᴹ (E Aᴹ) σᴹ ⌜ Aᴹ ⌝) ]
SC!ᵐ .SCᴹ.idSᴹ = idSᴹ
SC!ᵐ .SCᴹ._∘ᴹ_ = _∘ᴹ_
SC!ᵐ .SCᴹ.π₁ᴹ = π₁ᴹ
SC!ᵐ .SCᴹ.π₂ᴹ {Aᴹ = Aᴹ} σᴹ =
 (Aᴹ [ π₁ᴹ σᴹ ]T!) , π₂ᴹ σᴹ , tyOfπ₂ᴹ σᴹ ∙ [∘]Tᴹ (E Aᴹ) (π₁ᴹ σᴹ) ⌜ Aᴹ ⌝
SC!ᵐ .SCᴹ.tyOfπ₂ᴹ {Δᴹ} {Γᴹ} {Aᴹ} σᴹ = refl
SC!ᵐ .SCᴹ.idS∘ᴹ_ = idS∘ᴹ_
SC!ᵐ .SCᴹ._∘idSᴹ = _∘idSᴹ
SC!ᵐ .SCᴹ.assocSᴹ = assocSᴹ
SC!ᵐ .SCᴹ.[idS]Tᴹ {Γᴹ} {Aᴹ} =
 cong (ty³ (Aᴹ .V) (E Aᴹ)) (sym (⌜ Aᴹ ⌝ ∘idSᴹ))
SC!ᵐ .SCᴹ.[∘]Tᴹ {Θᴹ} {Γᴹ} {Δᴹ} Aᴹ σᴹ τᴹ =
 cong (ty³ (Aᴹ .V) (E Aᴹ)) (assocSᴹ σᴹ τᴹ ⌜ Aᴹ ⌝)
SC!ᵐ .SCᴹ.,∘ᴹ {Aᴹ = Aᴹ} σᴹ (Bᴹ , t , r) τᴹ p q = ,∘ᴹ σᴹ t τᴹ _ _
SC!ᵐ .SCᴹ.ηπᴹ σᴹ = ηπᴹ σᴹ ∙ cong,∶[] _ _ refl refl
SC!ᵐ .SCᴹ.η∅ᴹ = η∅ᴹ
SC!ᵐ .SCᴹ.βπ₁ᴹ σᴹ (Bᴹ , t , q) p =  βπ₁ᴹ σᴹ t _
SC!ᵐ .SCᴹ.βπ₂ᴹ {Aᴹ = Aᴹ} σᴹ (Bᴹ , t , q) p =
 Tm!-≡ (cong (Aᴹ [_]T!) (βπ₁ᴹ σᴹ t _) ∙ sym p) (βπ₂ᴹ σᴹ t _)
SC!ᵐ .SCᴹ.[idS]tᴹ (Bᴹ , t , q) = Tm!-≡ (SC!ᵐ .SCᴹ.[idS]Tᴹ) ([idS]tᴹ t)
SC!ᵐ .SCᴹ.[∘]tᴹ (Bᴹ , t , q) σᴹ τᴹ =
 Tm!-≡ (SC!ᵐ .SCᴹ.[∘]Tᴹ Bᴹ σᴹ τᴹ) ([∘]tᴹ t σᴹ τᴹ)
SC!ᵐ .SCᴹ.Uᴹ = ty³ ∅ᴹ Uᴹ ∅Sᴹ
SC!ᵐ .SCᴹ.U[]ᴹ {σᴹ = σᴹ} = cong (ty³ ∅ᴹ Uᴹ) (η∅ᴹ (∅Sᴹ ∘ᴹ σᴹ))
