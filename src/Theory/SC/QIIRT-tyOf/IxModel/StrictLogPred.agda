{-# OPTIONS --lossy-unification #-}
module Theory.SC.QIIRT-tyOf.IxModel.StrictLogPred where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

open import Theory.SC.QIIRT-tyOf.Model.Term
open import Theory.SC.QIIRT-tyOf.Model.StrictTerm
open SC Termₛ
open Var

open import Theory.SC.QIIRT-tyOf.DisplayedModel Termₛ


record Ctxᴾ (Γ : Ctx) : Set where
  constructor cᵖ
  field
    ctxᴾ : Ctx
    wkᴾ  : Sub ctxᴾ Γ
open Ctxᴾ

Tyᴾ : Ctxᴾ Γ → Ty Γ →  Set
-- Tyᴾ Γᴾ A = Ty (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ])
Tyᴾ Γᴾ A = Σ[ Δ ∈ Ctx ] (Δ ≡ (ctxᴾ Γᴾ ,C A [ wkᴾ Γᴾ ]T)) × Ty Δ

ι : {Γᴾ : Ctxᴾ Γ} → {A : Ty Γ} → Tyᴾ Γᴾ A → Ty (ctxᴾ Γᴾ ,C A [ wkᴾ Γᴾ ]T)
ι (Δ , r , Aᴾ) = subst Ty r Aᴾ

ι⁻¹ : {Γᴾ : Ctxᴾ Γ} → {A : Ty Γ} → Ty (ctxᴾ Γᴾ ,C A [ wkᴾ Γᴾ ]T) → Tyᴾ Γᴾ A
ι⁻¹ Aᴾ = _ , refl , Aᴾ

ιι⁻¹ : {Γᴾ : Ctxᴾ Γ} → {A : Ty Γ} → (A : Ty (ctxᴾ Γᴾ ,C A [ wkᴾ Γᴾ ]T)) → ι (ι⁻¹ A) ≡ A
ιι⁻¹ A = substRefl {B = Ty} A

ι⁻¹ι : {Γᴾ : Ctxᴾ Γ} → {A : Ty Γ} → (Aᴾ : Tyᴾ Γᴾ A) → ι⁻¹ (ι Aᴾ) ≡ Aᴾ
ι⁻¹ι {Γᴾ = Γᴾ} {A = A} (Δ , r , Aᴾ) = lemma r Aᴾ
 where
  lemma : {A : Type}{B : A → Type}{a a' : A}
        → (r : a ≡ a')(b : B a)
        → _≡_ {A = Σ[ a ∈ A ] ((a ≡ a') × B a)} (a' , refl , subst B r b) (a , r , b)
  lemma {A} {B} {a} {a'} r b = J (λ a' r → _≡_ {A = Σ[ a ∈ A ] ((a ≡ a') × B a)} (a' , refl , subst B r b) (a , r , b)) (λ i → (a , refl , substRefl {B = B} b i)) r


record Subᴾ (Γᴾ : Ctxᴾ Γ)(Δᴾ : Ctxᴾ Δ)(σ : Sub Γ Δ) : Set where
  constructor sᴾ
  field
    subᴾ : Sub (ctxᴾ Γᴾ) (ctxᴾ Δᴾ)
    wkᴾnat : wkᴾ Δᴾ ∘ subᴾ ≡ σ ∘ wkᴾ Γᴾ
open Subᴾ

[wkᴾnat] : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{σ : Sub Γ Δ}
         → (A : Ty Δ)(σᴾ : Subᴾ Γᴾ Δᴾ σ)
         → _≡_ {A = Ty (ctxᴾ Γᴾ)} (A [ wkᴾ Δᴾ ]T [ subᴾ σᴾ ]T) (A [ σ ]T [ wkᴾ Γᴾ ]T)
[wkᴾnat] {Γᴾ = Γᴾ} {Δᴾ} {σ} A σᴾ = cong (A [_]T) (wkᴾnat σᴾ)


≡-Subᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{σ : I → Sub Γ Δ}
       → (σᴾ : Subᴾ Γᴾ Δᴾ (σ i0)) → (τᴾ : Subᴾ Γᴾ Δᴾ (σ i1))
       → subᴾ σᴾ ≡ subᴾ τᴾ → PathP (λ i → Subᴾ Γᴾ Δᴾ (σ i)) σᴾ τᴾ
≡-Subᴾ σᴾ τᴾ eq i .subᴾ = eq i
≡-Subᴾ {Γᴾ = Γᴾ} {Δᴾ} {σ} σᴾ τᴾ eq i .wkᴾnat =
 isProp→PathP {B = λ i → (wkᴾ Δᴾ) ∘ eq i ≡ σ i ∘ wkᴾ Γᴾ} (λ i → Sub-is-set _ _) (σᴾ .wkᴾnat) (τᴾ .wkᴾnat) i


Tmᴾ : (Γᴾ : Ctxᴾ Γ) → (t : Tm Γ) → Set
Tmᴾ Γᴾ t = Σ[ Aᴾ ∈ Tyᴾ Γᴾ (tyOf t) ] Σ[ t' ∈ Tm (ctxᴾ Γᴾ) ]
  tyOf t' ≡ (ι Aᴾ) [ idS , t [ wkᴾ Γᴾ ]t ∶[ [idS]T ] ]T

tyOfᴾ : {Γ : Ctx} {t : Tm Γ} {Γᴹ : Ctxᴾ Γ} → Tmᴾ Γᴹ t → Tyᴾ Γᴹ (tyOf t)
tyOfᴾ {Γ} {t} {Γᴾ} (Aᴾ , t' , p) = Aᴾ

open SC∙

LogPredᵃ : Motive∙ _ _ _ _
LogPredᵃ = record
  { Ctx∙  = Ctxᴾ
  ; Ty∙   = Tyᴾ
  ; Sub∙  = Subᴾ
  ; Tm∙   = Tmᴾ
  ; tyOf∙ = λ {Γ} {t} → tyOfᴾ {Γ} {t}
  ; Ty∙-is-set = Tyᴾ-is-set
  ; Tm∙-is-set = λ Γ∙ t → isSetΣ (Tyᴾ-is-set Γ∙ (tyOf t)) λ t∙ → isSetΣ Tm-is-set λ t' → isProp→isSet (Ty-is-set _ _)
  ; Sub∙-is-set = λ Γ∙ Δ∙ σ → isSetRetract f g (λ x → refl) (isSetΣ Sub-is-set λ τ → isProp→isSet (Sub-is-set _ _))
  }
 where
  Tyᴾ-is-set : (Γ∙ : Ctxᴾ Γ) → (A : Ty Γ) → isSet (Tyᴾ Γ∙ A)
  Tyᴾ-is-set = λ Γ∙ A → isSetΣ Ctx-is-Set λ Δ → isSet× (isProp→isSet (Ctx-is-Set _ _)) Ty-is-set

  f : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{σ : Sub Γ Δ}
    → Subᴾ Γᴾ Δᴾ σ → Σ[ δ ∈ (Sub (ctxᴾ Γᴾ) (ctxᴾ Δᴾ)) ] wkᴾ Δᴾ ∘ δ ≡ σ ∘ wkᴾ Γᴾ
  f σᴾ = subᴾ σᴾ , wkᴾnat σᴾ

  g : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{σ : Sub Γ Δ}
    → Σ[ δ ∈ (Sub (ctxᴾ Γᴾ) (ctxᴾ Δᴾ)) ] wkᴾ Δᴾ ∘ δ ≡ σ ∘ wkᴾ Γᴾ → Subᴾ Γᴾ Δᴾ σ
  g (δ , p) = record { subᴾ = δ ; wkᴾnat = p }

open IsSC∙
-- open Motive∙ LogPredᵃ

LogPredᵐ : IsSC∙ LogPredᵃ
LogPredᵐ .∅∙ = cᵖ ∅ ∅S
LogPredᵐ ._,∙_ {A = A} Γᵖ Aᴾ = cᵖ (ctxᴾ Γᵖ ,C A [ wkᴾ Γᵖ ]T ,C ι Aᴾ) ((wkᴾ Γᵖ ↑ A) ∘ π₁ idS)
LogPredᵐ ._[_]T∙ {Δ∙ = Δᴾ} {A} {Γ∙ = Γᴾ} Aᴾ σᴾ =
 _ , cong (Γᴾ .ctxᴾ ,C_) ([wkᴾnat] A σᴾ) , (ι Aᴾ) [ subᴾ σᴾ ↑ (A [ wkᴾ Δᴾ ]T) ]T
LogPredᵐ ._[_]t∙ {Δ} {Δᴾ} {t} {Γ} {Γᴾ} {σ} tᴾ σᴾ =
 ι⁻¹ (tyOf (π₂ idS)) ,
 t [ wkᴾ Δᴾ ]t [ subᴾ σᴾ ]t ,
 (cong (tyOf t [_]T) lemma ∙ sym (cong (_[ idS , t [ σ ]t [ wkᴾ Γᴾ ]t ∶[ [idS]T ] ]T) ((ιι⁻¹ _) ∙ tyOfπ₂ idS)))
  where
   lemma : wkᴾ Δᴾ ∘ subᴾ σᴾ ≡ σ ∘ wkᴾ Γᴾ ∘ π₁ idS ∘ (idS , t [ σ ]t [ wkᴾ Γᴾ ]t ∶[ [idS]T ])
   lemma = wkᴾnat σᴾ ∙ sym ((σ ∘ wkᴾ Γᴾ) ∘idS) ∙ cong ((σ ∘ wkᴾ Γᴾ) ∘_) (sym (βπ₁ idS (t [ σ ]t [ wkᴾ Γᴾ ]t) [idS]T))
LogPredᵐ .tyOf[]∙ {Δ∙ = Δ∙} {t} {Γ∙ = Γ∙} {σ} {t∙ = t∙} {σ∙ = σ∙} = {!!}
LogPredᵐ .∅S∙ = sᴾ ∅S refl
LogPredᵐ ._,_∶[_,_]∙ = {!!}
LogPredᵐ .idS∙ = sᴾ idS refl
LogPredᵐ ._∘∙_ {τ = τ} σᵖ τᵖ =
 sᴾ (subᴾ σᵖ ∘ subᴾ τᵖ)
    (cong (_∘ subᴾ τᵖ) (wkᴾnat σᵖ) ∙ cong (τ ∘_) (wkᴾnat τᵖ))
LogPredᵐ .π₁∙ {Γ} {Γᴾ} {Δ} {Δᴾ} {A} {Aᴾ} {σ} σᴾ = sᴾ (π₁ (π₁ (subᴾ σᴾ))) {!!}
LogPredᵐ .π₂∙ = {!!}
LogPredᵐ .tyOfπ₂∙ = {!!}
LogPredᵐ .idS∘∙_ σ∙ = ≡-Subᴾ _ _ refl
LogPredᵐ ._∘idS∙ σ∙ = ≡-Subᴾ _ _ refl
LogPredᵐ .assocS∙ σ∙ τ∙ γ∙ = ≡-Subᴾ _ _ refl
LogPredᵐ .,∘∙ σ∙ t∙ τ∙ p p∙ q q∙ = ≡-Subᴾ _ _ {!!}
LogPredᵐ .ηπ∙ = {!!}
LogPredᵐ .η∅∙ σ∙ = ≡-Subᴾ _ _ (η∅ (subᴾ σ∙))
LogPredᵐ .βπ₁∙ = {!!}
LogPredᵐ .βπ₂∙ = {!!}
LogPredᵐ .[idS]T∙ A∙ = {!!}
LogPredᵐ .[∘]T∙ = {!!}
LogPredᵐ .[idS]t∙ = {!!}
LogPredᵐ .[∘]t∙ t∙ σ∙ τ∙ = {!!}
LogPredᵐ .U∙ = {!!}
LogPredᵐ .U[]∙ = {!!}


{-
LogPredᵐ ._[_]t∙ {Δ} {Δᴾ} {t} {Γ} {Γᴾ} {σ} tᴾ σᴾ =
  ι⁻¹ (tyOf (π₂ idS)) , t [ wkᴾ Δᴾ ] [ subᴾ σᴾ ] , [∘]T _ _ _ ∙ (λ i → tyOf t [ lemma i ]) ∙ sym ([∘]T _ _ _ ∙ [∘]T _ _ _ ∙ [∘]T _ _ _) ∙ cong (_[ idS , t [ σ ] [ wkᴾ Γᴾ ] ∶[ [idS]T ] ]) (sym (ιι⁻¹ _))
   where
    lemma : wkᴾ Δᴾ ∘ subᴾ σᴾ ≡ σ ∘ (wkᴾ Γᴾ ∘ (π₁ idS ∘ (idS , t [ σ ]t [ wkᴾ Γᴾ ]t ∶[ [idS]T ])))
    lemma = wkᴾnat σᴾ ∙ cong (σ ∘_) (sym (wkᴾ Γᴾ ∘idS) ∙
                                    cong (wkᴾ Γᴾ ∘_) (sym (βπ₁ _ _ _) ∙
                                                     cong π₁ (sym (idS∘ _)) ∙
                                                     π₁∘ idS (idS , t [ σ ] [ wkᴾ Γᴾ ] ∶[ [idS]T ])))

LogPredᵐ .tyOf[]∙ {Δ∙ = Δ∙} {t} {Γ∙ = Γ∙} {σ} {t∙ = t∙} {σ∙ = σ∙} = cong ι⁻¹ goal ∙ ι⁻¹ι _
 where
  goal : tyOf t [ σ ] [ wkᴾ Γ∙ ] [ π₁ idS ] ≡ subst Ty (cong (Γ∙ .ctxᴾ ,_) ([wkᴾnat] (tyOf t) σ∙)) (ι (tyOfᴾ t∙) [ subᴾ σ∙ ↑ (tyOf t [ wkᴾ Δ∙ ]) ])
  goal = fromPathP⁻ goal'
   where
    goal' : PathP (λ i → Ty (cong (Γ∙ .ctxᴾ ,_) ([wkᴾnat] (tyOf t) σ∙) (~ i))) (tyOf t [ σ ] [ wkᴾ Γ∙ ] [ π₁ idS ]) (ι (tyOfᴾ t∙) [ subᴾ σ∙ ↑ (tyOf t [ wkᴾ Δ∙ ]) ])
    goal' = {!!}
-- Ty (Γ∙ .ctxᴾ Foo., tyOf t Foo.[ wkᴾ Δ∙ ]T Foo.[ subᴾ σ∙ ]T)
-- Ty (Γ∙ .ctxᴾ Foo., tyOf t [ σ ] [ wkᴾ Γ∙ ])
LogPredᵐ ._,_∶[_,_]∙ {Γ} {Γ∙} {Δ} {Δ∙} {σ} {A} {t = t} σ∙ {A∙} (Aᴾ , t∙ , r) p q .subᴾ = (subᴾ σ∙ , t [ wkᴾ Γ∙  ] ∶[ cong (_[ wkᴾ Γ∙ ]) p ∙ sym ([wkᴾnat] A σ∙) ] , t∙ ∶[ r ∙ {!fromPathP q!} ])
_,_∶[_,_]∙ LogPredᵐ σ∙ {A∙} t∙ p q .wkᴾnat = {!!}
LogPredᵐ .π₁∙ {Γ} {Γᴾ} {Δ} {Δᴾ} {A} {Aᴾ} {σ} σᴾ = record
  { subᴾ = π₁ (π₁ (subᴾ σᴾ))
  ; wkᴾnat =
      wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ))
        ≡⟨ cong (wkᴾ Δᴾ ∘_) (π₁idS (π₁ (subᴾ σᴾ))) ⟩
      wkᴾ Δᴾ ∘ (π₁ idS ∘ π₁ (subᴾ σᴾ))
        ≡⟨ sym (assocS _ _ _) ⟩
      (wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)
        ≡⟨ sym (βπ₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)) (π₂ idS [ π₁ (subᴾ σᴾ) ]) _) ⟩
      π₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ])
        ≡⟨ cong π₁
          ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ]
            ≡⟨ sym (⟨,∘⟩ (wkᴾ Δᴾ ∘ π₁ idS) (π₂ idS) (π₁ (subᴾ σᴾ)) tyOfπ₂idS) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ π₁ (subᴾ σᴾ)
            ≡⟨ cong ((wkᴾ Δᴾ ↑ A) ∘_) (π₁idS (subᴾ σᴾ)) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ (π₁ idS ∘ subᴾ σᴾ)
            ≡⟨ sym (assocS _ _ _) ⟩
          ((wkᴾ Δᴾ ↑ A) ∘ π₁ idS) ∘ subᴾ σᴾ
            ≡⟨ wkᴾnat σᴾ ⟩
          σ ∘ wkᴾ Γᴾ
            ∎)
        ⟩
      π₁ (σ ∘ wkᴾ Γᴾ)
        ≡⟨ π₁∘ σ (wkᴾ Γᴾ) ⟩
      π₁ σ ∘ wkᴾ Γᴾ
        ∎
  }
LogPredᵐ .π₂∙ {Γ} {Γᴾ} {Δ} {Δᴾ} {A} {Aᴾ} {σ} σᴾ =
  ι⁻¹ ((ι Aᴾ) [ π₁ (subᴾ σᴾ) ∘ wk ]) , π₂ (subᴾ σᴾ) , {!!} -- cong (ι Aᴾ [_]) q ∙ sym ([∘]T _ _ _) ∙ {!cong (_[ sym (ιι⁻¹ _)!}
  -- _ _ _ ∙ cong (A [_]) p ∙ {!tyOf (π₂ (subᴾ σᴾ))!}
  -- A [ π₁ σ ∘ (wkᴾ Γᴾ ∘ wk) ] , π₂ (π₁ (subᴾ σᴾ)) , [∘]T _ _ _ ∙ cong (A [_]) p ∙ sym ([∘]T _ _ _)
  where
    q : π₁ (subᴾ σᴾ) ≡ (π₁ (subᴾ σᴾ) ∘ π₁ idS) ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ])
    q = π₁ (subᴾ σᴾ)
          ≡⟨ sym (π₁ (subᴾ σᴾ) ∘idS) ⟩
        π₁ (subᴾ σᴾ) ∘ idS
          ≡⟨ cong (π₁ (subᴾ σᴾ) ∘_) (sym (βπ₁ _ _ _)) ⟩
        π₁ (subᴾ σᴾ) ∘ (π₁ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ]))
          ≡⟨ cong (λ z → π₁ (subᴾ σᴾ) ∘ (π₁ z)) (sym (idS∘ _)) ⟩
        π₁ (subᴾ σᴾ) ∘ (π₁ (idS ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ])))
          ≡⟨ cong (π₁ (subᴾ σᴾ) ∘_) (π₁∘ _ _) ⟩
        π₁ (subᴾ σᴾ) ∘ (π₁ idS ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ]))
          ≡⟨ sym (assocS _ _ _) ⟩
        (π₁ (subᴾ σᴾ) ∘ π₁ idS) ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ])
          ∎
{-    p : wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ)) ≡ π₁ σ ∘ wkᴾ Γᴾ -- (π₁ σ ∘ (wkᴾ Γᴾ ∘ π₁ idS)) ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ])
    p =
      wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ))
        ≡⟨ cong (wkᴾ Δᴾ ∘_) (π₁idS (π₁ (subᴾ σᴾ))) ⟩
      wkᴾ Δᴾ ∘ (π₁ idS ∘ π₁ (subᴾ σᴾ))
        ≡⟨ sym (assocS _ _ _) ⟩
      (wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)
        ≡⟨ sym (βπ₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)) (π₂ idS [ π₁ (subᴾ σᴾ) ]) _) ⟩
      π₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ])
        ≡⟨ cong π₁
          ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ]
            ≡⟨ sym (⟨,∘⟩ (wkᴾ Δᴾ ∘ π₁ idS) (π₂ idS) (π₁ (subᴾ σᴾ)) tyOfπ₂idS) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ π₁ (subᴾ σᴾ)
            ≡⟨ cong ((wkᴾ Δᴾ ↑ A) ∘_) (π₁idS (subᴾ σᴾ)) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ (π₁ idS ∘ subᴾ σᴾ)
            ≡⟨ sym (assocS _ _ _) ⟩
          ((wkᴾ Δᴾ ↑ A) ∘ π₁ idS) ∘ subᴾ σᴾ
            ≡⟨ wkᴾnat σᴾ ⟩
          σ ∘ wkᴾ Γᴾ
            ∎)
        ⟩
      π₁ (σ ∘ wkᴾ Γᴾ)
        ≡⟨ π₁∘ σ (wkᴾ Γᴾ) ⟩
      π₁ σ ∘ wkᴾ Γᴾ
{-        ≡⟨ sym ((π₁ σ ∘ wkᴾ Γᴾ) ∘idS) ⟩
      (π₁ σ ∘ wkᴾ Γᴾ) ∘ idS
        ≡⟨ cong ((π₁ σ ∘ wkᴾ Γᴾ) ∘_) (sym (cong π₁ (idS∘ _) ∙ βπ₁ _ _ _) ∙ π₁∘ idS _) ⟩
      (π₁ σ ∘ wkᴾ Γᴾ) ∘ (π₁ idS ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ]))
        ≡⟨ sym (assocS (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ]) (π₁ idS) (π₁ σ ∘ wkᴾ Γᴾ)) ∙ cong (_∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ])) (assocS (π₁ idS) (wkᴾ Γᴾ) (π₁ σ)) ⟩
      (π₁ σ ∘ (wkᴾ Γᴾ ∘ π₁ idS)) ∘ (idS , π₂ σ [ wkᴾ Γᴾ ] ∶[ [idS]T ])
-}
        ∎ -}
LogPredᵐ .[idS]T∙  {Γ} {Γᴾ} {A} Aᴾ =
 {!toPathP (cong (transport (λ i → Ty (ctxᴾ Γᴾ , ([idS]T i [ wkᴾ Γᴾ ])))) ([idS]T {A = {!Aᴾ!}}) ∙ {!!})!}
LogPredᵐ .U∙ = ι⁻¹ U
LogPredᵐ .tyOfπ₂∙ {Γ} {Γᴾ} {Δ} {Δᴾ} {A} {Aᴾ} {σ} σᴾ = cong (Aᴾ [_]) (goal {!!})
 where
  goal : ∀ p → π₁ (subᴾ σᴾ) ∘ wk ≡ transport p (π₁ (π₁ (subᴾ σᴾ)) ↑ (A [ wkᴾ Δᴾ ]))
  goal p = {!!}
(idS∘∙ LogPredᵐ) {σ = σ} σ∙ = ≡-Subᴾ {σ = λ i → (idS∘ σ) i} (_∘∙_ LogPredᵐ (idS∙ LogPredᵐ) σ∙) σ∙ (idS∘ subᴾ σ∙)
LogPredᵐ ._∘idS∙ {σ = σ} σ∙ = ≡-Subᴾ {σ = λ i → (σ ∘idS) i} (_∘∙_ LogPredᵐ σ∙ (idS∙ LogPredᵐ)) σ∙ (subᴾ σ∙ ∘idS)
LogPredᵐ .assocS∙ {σ = σ} {τ = τ} {γ = γ} σ∙ τ∙ γ∙ = ≡-Subᴾ {σ = λ i → (assocS σ τ γ) i} (_∘∙_ LogPredᵐ (_∘∙_ LogPredᵐ γ∙ τ∙) σ∙) (_∘∙_ LogPredᵐ γ∙ (_∘∙_ LogPredᵐ τ∙ σ∙)) (assocS _ _ _)
LogPredᵐ .,∘∙ σ∙ t∙ τ∙ p₁ p∙ q q∙ = toPathP {!!}
LogPredᵐ .ηπ∙ σ∙ = {!!}
LogPredᵐ .η∅∙ {σ = σ} σ∙ = ≡-Subᴾ {σ = λ i → η∅ σ i} σ∙ (LogPredᵐ .∅S∙) (η∅ (subᴾ σ∙))
LogPredᵐ .βπ₁∙ σ∙ t∙ p₁ p∙ = {!!}
LogPredᵐ .βπ₂∙ σ∙ t∙ p₁ p∙ q q∙ = {!!}
LogPredᵐ .[∘]T∙ A∙ σ∙ τ∙ = {!!}
LogPredᵐ .[idS]t∙ t∙ = {!!}
LogPredᵐ .[∘]t∙ t∙ σ∙ τ∙ = {!!}
LogPredᵐ .U[]∙ {Γ} {Δ} {σ} {Γ∙} {Δ∙} {σ∙} = {!!}
{- where
  lemma : (p : (U [ σ ]) ≡ U)
        → (q : U [ wkᴾ Δ∙ ] [ subᴾ σ∙ ] ≡ U [ σ ] [ wkᴾ Γ∙ ])
        → transport (cong (Tyᴾ Γ∙) p) (U [ transport (cong (λ - → Sub (ctxᴾ Γ∙ , -) (ctxᴾ Δ∙ , (U [ wkᴾ Δ∙ ]))) q) (subᴾ σ∙ ↑ (U [ wkᴾ Δ∙ ])) ]) ≡ U [ transport ((cong (λ - → Sub (ctxᴾ Γ∙ , -) (ctxᴾ Δ∙ , (U [ wkᴾ Δ∙ ]))) q) ∙ cong (λ - → Sub (ctxᴾ Γ∙ , (- [ wkᴾ Γ∙ ])) (ctxᴾ Δ∙ , (U [ wkᴾ Δ∙ ]))) p) (subᴾ σ∙ ↑ (U [ wkᴾ Δ∙ ])) ]
  lemma p q = {!!}-}

-- foo : {X Y : Type} → (p : X ≡ Y) → {x : X} → _≡_ {A = Σ[ X ∈ Type ] X} (X , x) (Y , transport p x)
-- foo {X} p {x} = J {x = X} (λ Y p → (X , x) ≡ (Y , transport p x)) (λ i → (X , transportRefl x (~ i))) p
-}
