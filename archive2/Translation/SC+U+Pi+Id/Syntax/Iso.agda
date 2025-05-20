-- Invertibility of translation of syntax between QIIRT and QIIT
open import Prelude
  -- renaming (_,_ to _,'_)

module Translation.SC+U+Pi+Id.Syntax.Iso where

import Translation.SC+U+Pi+Id.Syntax.Translate as ST
open ST.QIIRT→QIIT
open ST.QIIT→QIIRT

private
  _≡,≅_ : ∀{a b}{A : Set a}{B : A → Set b}{x x' : A}{y : B x}{y' : B x'}
        → x ≡ x' → y ≅ y' → _≡_ {A = Σ A B} (x , y) (x' , y')
  p ≡,≅ q = ≅-to-≡ $ hcong₂ _,_ (≡-to-≅ p) q

module <>≡id where
  open import Theory.SC+U+Pi+Id.QIIT.Syntax
  import Theory.SC+U+Pi+Id.QIIRT.Syntax as IR
  open ≅-Reasoning

  {-# TERMINATING #-}
  <>c  : (Γ : Ctx)     → (Γ <c)  >c  ≡ Γ
  <>ty : (A : Ty  Γ i) → (A <ty) >ty ≅ A
  <>s  : (σ : Sub Γ Δ) → (σ <s)  >s  ≅ σ
  <>tm : (t : Tm  Γ A) → (t <tm) >tm ≅ t
  <>c ∅       = refl 
  <>c (Γ , A) = apd₂ _,_ (<>c Γ)
                         (≅-to-≡ $ HEq.trans (tr≅ (λ Γ → Ty Γ _) (<>c Γ) ((A <ty) >ty))
                                             (<>ty A))
  <>ty {Γ}         ([_]_ {Δ} {i} σ A) = begin
    (IR.[ σ <s ] (A <ty)) >ty
      ≅⟨ ≡-to-≅ $ sym $ []>ty (σ <s) (A <ty) ⟩
    [ (σ <s) >s ] (A <ty) >ty
      ≅⟨ icong₂ (uncurry Sub) (cong₂ _,_ (<>c Γ) (<>c Δ)) [_]_ (<>s σ) (<>ty A) ⟩
    ([ σ ] A
      ∎)
  <>ty             (U i)              = hcong  (λ Γ → U {Γ} i)        (≡-to-≅ $ <>c _)
  <>ty {Γ} {i}     (El t)             = icong  (λ Γ → Tm Γ (U {Γ} i)) (<>c Γ) El   (<>tm t)
  <>ty {Γ} {suc i} (Lift A)           = icong  (λ Γ → Ty Γ i)         (<>c Γ) Lift (<>ty A)
  <>ty {Γ} {i}     (Π A B)            = icong₂ (λ Γ → Ty Γ i)         (<>c Γ) Π    (<>ty A) (<>ty B)
  <>ty {Γ} {i}     (Id a t u)         = icong₃ (λ Γ → Tm Γ (U {Γ} i)) (<>c Γ) Id   (<>tm a) (<>tm t) (<>tm u)
  <>s {Γ}  ∅                    =
    hcong {B = λ Γ → Sub Γ ∅} (λ Γ → ∅ {Γ}) (≡-to-≅ $ <>c Γ)
  <>s {Γ} (_,_ {Δ} {i} σ {A} t) =
    icong₂ {I = Ctx × ∃ (λ Δ → Ty Δ i)}
           (λ (Γ , (Δ , _)) → Sub Γ Δ)
           {λ {(Γ , (Δ , A))} σ → Tm Γ ([ σ ] A)}
           (cong₂ _,_ (<>c Γ) (<>c Δ ≡,≅ <>ty A))
           (λ {(Γ , (Δ , A))} σ t → _,ˢ_ σ {A} t)
           (<>s σ)
           (HEq.trans (tr≅ (Tm ((Γ <c) >c)) (sym $ []>ty (σ <s) (A <ty)) ((t <tm) >tm))
                      (<>tm t))
    where
      _,ˢ_ : ∀{Γ Δ} (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Γ ([ σ ] A)) → Sub Γ (Δ , A)
      _,ˢ_ = _,_
  <>s {Γ}  idS                  =
    hcong (λ Γ → idS {Γ}) (≡-to-≅ $ <>c Γ)
  <>s {Γ} (_⨟_ {Δ} {Θ} τ σ)     =
    icong₂ {I = Ctx × Ctx × Ctx}
           (λ (Γ , (Δ , Θ)) → Sub Γ Δ)
           {λ {(Γ , (Δ , Θ))} _ → Sub Δ Θ}
           (cong₂ _,_ (<>c Γ) (cong₂ _,_ (<>c Δ) (<>c Θ)))
            _⨟_
           (<>s τ)
           (<>s σ)
  <>s {Γ} (π₁ {Δ} {i} {A} σ)    =
    icong {I = Ctx × ∃ (λ Δ → Ty Δ i)}
          (λ (Γ , (Δ , A)) → Sub Γ (Δ , A))
          (cong₂ _,_ (<>c Γ) (<>c Δ ≡,≅ <>ty A))
           π₁
          (<>s σ) 
  <>tm {Γ}         (π₂ {_} {Δ} {i} {A} σ)   =
    HEq.trans (tr≅ (Tm ((Γ <c) >c)) ([]>ty (IR.π₁ (σ <s)) (A <ty)) (π₂ ((σ <s) >s))) 
              (icong {I = Ctx × ∃ (λ Δ → Ty Δ i)}
                     (λ (Γ , (Δ , A)) → Sub Γ (Δ , A))
                     (cong₂ _,_ (<>c Γ) (<>c Δ ≡,≅ <>ty A))
                      π₂
                     (<>s σ))
  <>tm {Γ} {i}     ([_]tm_ {Δ = Δ} σ {A} t) =
    HEq.trans (≡-to-≅ $ sym $ []>tm (σ <s) (t <tm))
              (HEq.trans (tr≅ (Tm ((Γ <c) >c)) ([]>ty (σ <s) (A <ty)) ([ (σ <s) >s ]tm (t <tm) >tm))
                         (icong₂ {I = Ctx × ∃ (λ Δ → Ty Δ i)} (λ (Γ , (Δ , _)) → Sub Γ Δ) 
                                 (cong₂ _,_ (<>c Γ) (<>c Δ ≡,≅ <>ty A))
                                 (λ {(_ , (_ , A))} σ t → [_]tm_ σ {A} t)
                                 (<>s σ)
                                 (<>tm t)))
  <>tm {Γ} {suc i} (c A)                    = icong (λ Γ → Ty Γ i) (<>c Γ) c (<>ty A)
  <>tm {Γ} {suc i} (mk {A = A} t)           = icong {I = ∃ (λ Γ → Ty Γ i)} (uncurry Tm) (<>c Γ ≡,≅ <>ty A) mk (<>tm t)
  <>tm {Γ} {i}     (un {A = A} t)           = icong {I = ∃ (λ Γ → Ty Γ i)} (λ (Γ , A) → Tm Γ (Lift A)) (<>c Γ ≡,≅ <>ty A) un (<>tm t)
  <>tm {Γ} {i}     (ƛ_ {A = A} {B = B} t)   = icong₂ {I = ∃ (λ Γ → Ty Γ i)}
                                                     (λ (Γ , A) → Ty (Γ , A) i)
                                                     (<>c Γ ≡,≅ <>ty A)
                                                     (λ B t → ƛ_ {B = B} t)
                                                     (<>ty B)
                                                     (<>tm t)
  <>tm {Γ , A} {i} (app {B = B} t)          = icong₂ {I = ∃ (λ Γ → Ty Γ i)}
                                                     (λ (Γ , A) → Ty (Γ , A) i)
                                                     (<>c Γ ≡,≅ <>ty A)
                                                     (λ B t → app {B = B} t)
                                                     (<>ty B)
                                                     (<>tm t)
  <>tm {Γ} {i}     (refl {a = a} t)         = icong₂ (λ Γ → Tm Γ (U {Γ} i))
                                                     (<>c Γ)
                                                     (λ a t → refl {a = a} t)
                                                     (<>tm a)
                                                     (<>tm t)


module ><≡id where
  open import Theory.SC+U+Pi+Id.QIIRT.Syntax
  open import Theory.SC+U+Pi+Id.QIIRT.Properties
  import Theory.SC+U+Pi+Id.QIIT.Syntax as I

  open ≅-Reasoning


  {-# TERMINATING #-}
  ><c  : (Γ : Ctx)     → (Γ >c)  <c  ≡ Γ
  ><ty : (A : Ty  Γ i) → (A >ty) <ty ≅ A
  ><s  : (σ : Sub Γ Δ) → (σ >s)  <s  ≅ σ
  ><tm : (t : Tm  Γ A) → (t >tm) <tm ≅ t

  ><c ∅       = refl
  ><c (Γ , A) = apd₂ _,_ (><c Γ) (≅-to-≡ $ HEq.trans (tr≅ (λ Γ → Ty Γ _) (><c Γ) ((A >ty) <ty))
                                                     (><ty A))
  ><ty             (U i)      = hcong  (λ Γ → U {Γ} i)        (≡-to-≅ $ ><c _)
  ><ty {Γ} {i}     (El t)     = icong  (λ Γ → Tm Γ (U {Γ} i)) (><c Γ) El   (><tm t)
  ><ty {Γ} {suc i} (Lift A)   = icong  (λ Γ → Ty Γ i)         (><c Γ) Lift (><ty A)
  ><ty {Γ} {i}     (Π A B)    = icong₂ (λ Γ → Ty Γ i)         (><c Γ) Π    (><ty A) (><ty B)
  ><ty {Γ} {i}     (Id a t u) = icong₃ (λ Γ → Tm Γ (U {Γ} i)) (><c Γ) Id   (><tm a) (><tm t) (><tm u)
  ><s {Γ} ∅ =
    hcong  {B = λ Γ → Sub Γ ∅} (λ Γ → ∅ {Γ}) (≡-to-≅ $ ><c Γ)
  ><s {Γ} (_,_ {Δ} {i} σ {A} t) =
    icong₂ {I = Ctx × ∃ (λ Δ → Ty Δ i)}
           (λ (Γ , (Δ , _)) → Sub Γ Δ)
           {λ {(Γ , (Δ , A))} σ → Tm Γ ([ σ ] A)}
           (cong₂ _,_ (><c Γ) (><c Δ ≡,≅ ><ty A))
           (λ {(Γ , (Δ , A))} σ t → _,ˢ_ σ {A} t)
           (><s σ)
           (HEq.trans (icong (I.Tm (Γ >c))
                             ([]>ty σ A)
                              _<tm
                             (tr≅ (I.Tm ((Γ >c))) (sym $ []>ty σ A) (t >tm)))
                      (><tm t))
    where
      _,ˢ_ : ∀{Γ Δ} (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Γ ([ σ ] A)) → Sub Γ (Δ , A)
      _,ˢ_ = _,_
  ><s {Γ} idS = 
    hcong (λ Γ → idS {Γ}) (≡-to-≅ $ ><c Γ)
  ><s {Γ} (_⨟_ {Δ} {Θ} τ σ) =
    icong₂ {I = Ctx × Ctx × Ctx}
           (λ (Γ , (Δ , Θ)) → Sub Γ Δ)
           {λ {(Γ , (Δ , Θ))} _ → Sub Δ Θ}
           (cong₂ _,_ (><c Γ) (cong₂ _,_ (><c Δ) (><c Θ)))
            _⨟_
           (><s τ)
           (><s σ)
  ><s {Γ} (π₁ {Δ} {i} {A} σ) =
    icong {I = Ctx × ∃ (λ Δ → Ty Δ i)}
          (λ (Γ , (Δ , A)) → Sub Γ (Δ , A))
          (cong₂ _,_ (><c Γ) (><c Δ ≡,≅ ><ty A))
          π₁
          (><s σ) 
  ><tm {Γ} (π₂ {_} {Δ} {i} {A} σ) =
    HEq.trans (icong (I.Tm (Γ >c))
                     (sym $ []>ty (π₁ σ) A)
                      _<tm
                     (tr≅ (I.Tm (Γ >c)) ([]>ty (π₁ σ) A) (I.π₂ (σ >s))))
              (icong {I = Ctx × ∃ (λ Δ → Ty Δ i)}
                     (λ (Γ , (Δ , A)) → Sub Γ (Δ , A))
                     (cong₂ _,_ (><c Γ) (><c Δ ≡,≅ ><ty A))
                      π₂
                     (><s σ))
  ><tm {Γ} {i} ([_]tm_ {Δ = Δ} σ {A} t) =
      HEq.trans (icong (I.Tm (Γ >c))
                       (sym $ []>ty σ A)
                        _<tm
                       (tr≅ (I.Tm (Γ >c)) ([]>ty σ A) (I.[ σ >s ]tm (t >tm))))
                (HEq.trans (≡-to-≅ $ sym $ []tm≡[]t ((t >tm) <tm) ((σ >s) <s))
                           (icong₂ {I = Ctx × ∃ (λ Δ → Ty Δ i)}
                                   (λ (Γ , (Δ , _)) → Sub Γ Δ)
                                   (cong₂ _,_ (><c Γ) (><c Δ ≡,≅ ><ty A))
                                   (λ {(_ , (_ , A))} σ t → [_]tm_ σ {A} t)
                                   (><s σ)
                                   (><tm t)))
  ><tm {Γ} {suc i} (c A) =
    icong (λ Γ → Ty Γ i) (><c Γ) c (><ty A)
  ><tm {Γ} {suc i} (mk {A = A} t) =
    icong {I = ∃ (λ Γ → Ty Γ i)} (uncurry Tm) (><c Γ ≡,≅ ><ty A) mk (><tm t)
  ><tm {Γ} {i} (un {A = A} t) =
    icong {I = ∃ (λ Γ → Ty Γ i)} (λ (Γ , A) → Tm Γ (Lift A)) (><c Γ ≡,≅ ><ty A) un (><tm t)
  ><tm {Γ} {i} (ƛ_ {A = A} {B = B} t) =
    icong₂ {I = ∃ (λ Γ → Ty Γ i)}
           (λ (Γ , A) → Ty (Γ , A) i)
           (><c Γ ≡,≅ ><ty A)
           (λ B t → ƛ_ {B = B} t)
           (><ty B)
           (><tm t)
  ><tm {Γ , A} {i} (app {B = B} t) =
    icong₂ {I = ∃ (λ Γ → Ty Γ i)}
           (λ (Γ , A) → Ty (Γ , A) i)
           (><c Γ ≡,≅ ><ty A)
           (λ B t → app {B = B} t)
           (><ty B)
           (><tm t)
  ><tm {Γ} {i} (refl {a = a} t) = 
    icong₂ (λ Γ → Tm Γ (U {Γ} i))
           (><c Γ)
           (λ a t → refl {a = a} t)
           (><tm a)
           (><tm t) 