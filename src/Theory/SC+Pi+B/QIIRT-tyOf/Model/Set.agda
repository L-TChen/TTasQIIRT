open import Prelude

module Theory.SC+Pi+B.QIIRT-tyOf.Model.Set where

open import Theory.SC.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model

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

stdModelPi : Pi stdModel
stdModelPi = record
  { Π = λ A B → λ γ → (x : A γ) → B (γ , x) 
  ; app = λ (ΠAB , t) B pt →
    B , λ (γ , a) → (transport (cong (λ A → A γ) pt) (t γ)) a
  ; tyOfapp = λ _ → refl
  ; abs = λ {Γ} {A} (B , t) →
    (λ γ → (x : A γ) → B (γ , x)) , λ γ x → t (γ , x) 
  ; tyOfabs = refl
  ; Π[]   = λ {_} {_} {A} σ B i γ → (x : A (σ γ)) → B (σ γ , {!transportRefl x (~ i)!})
  -- unfolding _∙_
  ; abs[] = {!!}
  ; Πβ    = {!!}
  ; Πη    = {!!}
  }

Bool' : {Γ : Type} → Γ → Type
Bool' = λ _ → Bool

stdModel𝓑 : 𝓑 stdModel
stdModel𝓑 = record
  { 𝔹   = Bool'
  ; 𝔹[] = λ _ → refl
  ; tt  = Bool' , λ _ → true
  ; ff  = Bool' , λ _ → false
  ; tyOftt = refl
  ; tyOfff = refl
  ; tt[] = λ _ → refl
  ; ff[] = λ _ → refl
  ; elim𝔹 = λ P t pt u pu b pb
    → (λ γ → P (γ , (transport (cong (λ A → A γ) pb) (b .snd γ))))
    , λ γ → elim-Bool {_} {λ x → P (γ , x)}
      (transport (cong (λ A → A γ) pt) (t .snd γ))
      (transport (cong (λ A → A γ) pu) (u .snd γ))
      (transport (cong (λ A → A γ) pb) (b .snd γ))
  ; tyOfelim𝔹 = λ t pt u pu b pb p → refl
  ; elim𝔹[] = λ P t pt u pu b pb pt₂ pu₂ pb₂ p → {!!}
  }
