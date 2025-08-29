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

transportRefl² : {A : Set} (a : A)
  → transport refl (transport refl a)
  ≡ a
transportRefl² a =
  transport refl (transport refl a)
    ≡⟨ cong (transport refl) (transportRefl a) ⟩
  transport refl a
    ≡⟨ transportRefl a ⟩
  a
    ∎

cong₄ : ∀ {ℓ'''''} →
        {A : Type ℓ'''}
        {B : A → Type ℓ''''}
        {C : (a : A) → (b : B a) → Type ℓ}
        {D : (a : A) (b : B a) → C a b → Type ℓ'}
        {E : (a : A) (b : B a) → (c : C a b) → D a b c → Type ℓ'''''}
        (f : (a : A) (b : B a) (c : C a b) → (d : D a b c) → E a b c d) →
        {x y : A} (p : x ≡ y)
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v)
        {s : C x u} {t : C y v} (r : PathP (λ i → C (p i) (q i)) s t)
        {h : D x u s}{k : D y v t} (w : PathP (λ i → D (p i) (q i) (r i)) h k)
      → PathP (λ i → E (p i) (q i) (r i) (w i)) (f x u s h) (f y v t k)
cong₄ f p q r w i = f (p i) (q i) (r i) (w i)
{-# INLINE cong₄ #-}

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
  stdModelPi .Πη {Γ} {A} {B} (A' , t) pt i = pt (~ i) , λ γ → transport-filler (λ i → pt i γ) (t γ) (~ i)

Bool' : {Γ : Type} → Γ → Type
Bool' = λ _ → Bool

stdModel𝓑 : 𝓑 stdModel
stdModel𝓑 .𝓑.𝔹 = Bool'
stdModel𝓑 .𝓑.𝔹[] _ = refl
stdModel𝓑 .𝓑.tt = Bool' , λ _ → true
stdModel𝓑 .𝓑.ff = Bool' , λ _ → false
stdModel𝓑 .𝓑.tyOftt = refl
stdModel𝓑 .𝓑.tyOfff = refl
stdModel𝓑 .𝓑.tt[] _ = refl
stdModel𝓑 .𝓑.ff[] _ = refl
stdModel𝓑 .𝓑.elim𝔹 P t pt u pu b pb = (λ γ → P (γ , subst (λ A → A γ) pb (b .snd γ)))
                                    , λ γ → Bool-elim (λ x → P (γ , x))
                                                      (subst (λ A → A γ) pt (t .snd γ))
                                                      (subst (λ A → A γ) pu (u .snd γ))
                                                      (subst (λ A → A γ) pb (b .snd γ))
stdModel𝓑 .𝓑.tyOfelim𝔹 t pt u pu b pb p = refl
stdModel𝓑 .𝓑.elim𝔹[] {Γ} {Δ} {σ = σ} P t pt u pu b pb pt₂ pu₂ pb₂ p i .fst = p i
stdModel𝓑 .𝓑.elim𝔹[] {Γ} {Δ} {σ = σ} P t pt u pu b pb pt₂ pu₂ pb₂ p i .snd γ = ?

{-cong₄ Bool-elim {x = λ x → P (σ γ , x)} {y = P' γ} lem₀ {u = transport (λ j → pt j (σ γ)) (t .snd (σ γ))} {v = transport (λ j → pt₂ j γ) (t .snd (σ γ))} {!!} {s = transport (λ j → pu j (σ γ)) (u .snd (σ γ))} {t = transport (λ j → pu₂ j γ) (u .snd (σ γ))} {!!} {h = transport (λ j → pb j (σ γ)) (b .snd (σ γ))} {k = transport (λ j → pb₂ j γ) (b .snd (σ γ))} {!!} i
 where
  P' : ∀ γ → Bool → Type
  P' γ = λ x → P (σ γ , transport (λ j → step-≡ Bool' (step-≡ Bool' (step-≡ Bool' (Bool' ∎) refl) refl) refl j (γ , x)) x)
  lem₀ : (λ x → P (σ γ , x)) ≡ P' γ
  lem₀ i false = P (σ γ , {!transport-filler (λ i₂ →
            step-≡ (λ _ → Bool)
            (step-≡ (λ _ → Bool)
             (step-≡ (λ _ → Bool) ((λ _ → Bool) ∎) (λ _ _ → Bool))
             (λ _ _ → Bool))
            (λ _ _ → Bool) i₂ (γ , false)) false i!})
  lem₀ i true = P (σ γ , {!!})



{-
Bool-elim (λ x → p i γ) {!lem₁ γ i!} {!p i1 γ!} {!!}
 where
  P' : ∀ γ → Bool → Type
  P' γ x = P (σ γ , transport (λ j → step-≡ Bool' (step-≡ Bool' (step-≡ Bool' (Bool' ∎) refl) refl) refl j (γ , x)) x)
  q : ∀ γ x → x ≡ transport (λ j → step-≡ Bool' (step-≡ Bool' (step-≡ Bool' (Bool' ∎) refl) refl) refl j (γ , x)) x
  q γ x = {!!}
  lem : ∀ γ → PathP (λ i → p i γ)
                    (Bool-elim (λ x → P (σ γ , x))
                               (transport (λ j → pt j (σ γ)) (t .snd (σ γ)))
                               (transport (λ j → pu j (σ γ)) (u .snd (σ γ)))
                               (transport (λ j → pb j (σ γ)) (b .snd (σ γ))))
                    (Bool-elim (P' γ)
                               (transport (λ j → pt₂ j γ) (t .snd (σ γ)))
                               (transport (λ j → pu₂ j γ) (u .snd (σ γ)))
                               (transport (λ j → pb₂ j γ) (b .snd (σ γ))))
  lem γ i = Bool-elim (λ x → p i γ) (transport {!UIP (λ j → pt j (σ γ)) ? i!} (t .snd (σ γ))) {!!} {!!}
  
  lem₁ :  ∀ γ → PathP (λ i → P (σ γ , q γ true i)) (transport (λ j → pt j (σ γ)) (t .snd (σ γ))) (transport (λ j → pt₂ j γ) (t .snd (σ γ)))
  lem₁ = {!!}
-}
-}
