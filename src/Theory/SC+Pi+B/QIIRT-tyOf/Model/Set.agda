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

open SC stdModel
open Pi

transportRefl³ : {A : Set} (a : A)
  → transport refl (transport refl (transport refl a))
  ≡ a
transportRefl³ a =
  transport refl (transport refl (transport refl a))
    ≡⟨ cong (transport refl) (cong (transport refl) (transportRefl a)) ⟩
  transport refl (transport refl a)
    ≡⟨ cong (transport refl) (transportRefl a) ⟩
  transport refl a
    ≡⟨ transportRefl a ⟩
  a
    ∎
    
opaque
  unfolding _∙_
  stdModelPi : Pi stdModel
  stdModelPi .Π A B      = λ γ → (x : A γ) → B (γ , x) 
  stdModelPi .app t B pt =
    B , λ (γ , a) → (transport (cong (λ A → A γ) pt) (t .snd γ)) a
  stdModelPi .tyOfapp    = λ _ → refl
  stdModelPi .abs {Γ} {A} t =
    (λ γ → (a : A γ) → tyOf t (γ , a)) , λ γ a → t .snd (γ , a)
  stdModelPi .tyOfabs = refl
  stdModelPi .Π[] {Γ} {Δ} {A} σ B i γ =
    (a : A (σ γ)) → B (σ γ , transportRefl³ a (~ i))
  stdModelPi .abs[] {_} {_} {A} σ t i =
    (λ γ → (a : A (σ γ)) → t .fst (σ γ , transportRefl³ a (~ i))) ,
    λ γ a → t . snd (σ γ , transportRefl³ a (~ i)) 
  stdModelPi .Πβ {Γ} {A} t pt i = t .fst , λ γ → lem γ i
    where -- Yuck!
      lem : ∀ γ → transport (λ j → pt j (γ .fst)) (λ a → t .snd (γ .fst , a)) (γ .snd) ≡ t .snd γ
      lem (γ , a) =
        transport (λ j → pt j γ) (λ b → t .snd (γ , b)) a
          ≡⟨ cong (λ p → transport p (λ b → t .snd (γ , b)) a) (UIP (λ j → pt j γ) refl) ⟩
        transport (λ _ → (a : A γ) → t .fst (γ , a)) (λ b → t .snd (γ , b)) a
          ≡⟨ cong (λ (f : (a : A γ) → t .fst (γ , a)) → f a) (transportRefl (λ b → t .snd (γ , b))) ⟩
        t .snd (γ , a)
          ∎
  stdModelPi .Πη {Γ} {A} {B} t pt i = {!!}

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
  ; elim𝔹[] = λ P t pt u pu b pb pt₂ pu₂ pb₂ p i → ?
  }
