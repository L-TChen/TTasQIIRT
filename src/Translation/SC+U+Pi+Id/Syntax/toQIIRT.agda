open import Prelude
-- copy and modify from Theory
module Translation.SC+U+Pi+Id.Syntax.toQIIRT where

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Properties
open import Theory.SC+U+Pi+Id.QIIT.Recursion

open Recursor

private
  []ƛeq : {A : Ty Δ i}{B : Ty (Δ , A) i}(σ : Sub Γ Δ)(t : Tm (Δ , A) B)
        → tr (Tm Γ) (cong (λ τ → Π ([ σ ] A) ([ τ ] B)) (↑=⁺ A σ)) ([ σ ]t (ƛ t))
        ≡ ƛ ([ π₁ {A = [ σ ] A} idS ⨟ σ , π₂ idS ]tm t)
  []ƛeq {Δ} {i} {Γ} {A = A} {B} σ t = ≅-to-≡ $ begin
    tr (Tm Γ) _ ([ σ ]t (ƛ t))
      ≅⟨  tr≅ (Tm Γ) (cong (λ τ → Π ([ σ ] A) ([ τ ] B)) (↑=⁺ A σ)) ([ σ ]t (ƛ t))  ⟩
    [ σ ]t (ƛ t)
      ≅⟨ ≡-to-≅ $ []tm≡[]t (ƛ t) σ ⟨
    [ σ ]tm (ƛ t)
      ≅⟨ ≡-to-≅ $ []ƛ σ t ⟩
    ƛ ([ σ ↑ A ]tm t)
      ≅⟨ hcong (λ τ → ƛ ([ τ ]tm t)) (≡-to-≅ (↑=⁺ A σ)) ⟩
    (ƛ ([ wk ⨟ σ , vz ]tm t))
      ∎
     
    where open ≅-Reasoning

toQIIRT : Recursor
toQIIRT .mot = record
  { Ctxᴹ = Ctx
  ; Tyᴹ  = Ty
  ; Subᴹ = Sub
  ; Tmᴹ  = Tm
  }
toQIIRT .met = record
  { 𝒞    = record
    { [_]ᴹ_       = [_]_
    ; ∅ᶜᴹ         = ∅
    ; _,ᶜᴹ_       = _,_
    ; ∅ˢᴹ         = ∅
    ; _,ˢᴹ_       = _,_
    ; idSᴹ        = idS
    ; _⨟ᴹ_        = _⨟_
    ; π₁ᴹ         = π₁
    ; [idS]ᴹ      = [id]
    ; [⨟]ᴹ       = λ {Γ} {Δ} {σ} {Θ} {τ} {_} {A} → [⨟] {Γ} {Δ} {σ} {Θ} {τ} {_} {A}
    ; π₂ᴹ         = π₂
    ; [_]tmᴹ_     = [_]t_
    ; _⨟idSᴹ     = _⨟idS
    ; idS⨟ᴹ_     = idS⨟_
    ; ⨟-assocᴹ    = ⨟-assoc
    ; π₁,ᴹ      = π₁,
    ; ⨟,ᴹ       = λ {_} {Γ} {Δ} {Θ} {A} {σ} {τ} {t} → ⨟, ∙ cong (σ ⨟ τ ,_) ([]tm≡[]t t σ)
                  {- ⨟, ∙ cong (σ ⨟ τ ,_)
                              ([]tm≡[]t t σ 
                              ∙ sym (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t t)) (uip (sym [⨟]) refl)))
                  -}
    ; η∅ᴹ        = η∅
    ; η,ᴹ        = η,
    ; [idS]tmᴹ   = λ {_} {_} {_} {t} → refl -- cong (λ p → tr (TmᴹFam toQIIRT) p t) (uip [id] refl)
    ; [⨟]tmᴹ     = λ {_} {_} {σ} {_} {τ} {_} {_} {t}
                  → refl -- cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t [ τ ]t t)) (uip [⨟] refl)
    ; π₂,ᴹ      = λ {_} {_} {_} {A} {σ} {t} 
                  → begin
                    tr (λ τ → TmᴹFam toQIIRT ([ τ ] A)) π₁, (π₂ {A = A} (σ , t))
                      ≡⟨ tr-cong {P = TmᴹFam toQIIRT} {[_] A} π₁, ⟩
                    tr (TmᴹFam toQIIRT) (cong ([_] A) π₁,) (π₂ {A = A} (σ , t))
                      ≡⟨ cong (λ p → tr (TmᴹFam toQIIRT) p (π₂ {A = A} (σ , t)))
                              (uip (cong ([_] A) π₁,) refl) ⟩
                    π₂ (σ , t)
                      ≡⟨ π₂, ⟩
                    t
                      ∎
    }
  ; univ = record
    { Uᴹ       = U
    ; Elᴹ      = El
    ; Liftᴹ    = Lift
    ; cᴹ       = c
    ; mkᴹ      = mk
    ; unᴹ      = un
    ; []Uᴹ    = λ {_} {_} {σ} {i} → refl
    ; []Elᴹ   = λ σ u → refl
    ; []Liftᴹ = λ {_} {_} {σ} {i} {A} → refl
    ; []tcᴹ   = λ σ A → sym ([]tm≡[]t (c A) σ) ∙ []tc σ A
    ; []mkᴹ    = λ σ t → sym ([]tm≡[]t (mk t) σ) ∙ []mk σ t
    ; []unᴹ    = λ σ A t → sym ([]tm≡[]t (un t) σ) ∙ []un σ A t ∙ cong un ([]tm≡[]t t σ)
    ; Uβᴹ      = Uβ
    ; Uηᴹ      = Uη
    ; Liftβᴹ   = Liftβ
    ; Liftηᴹ   = Liftη
    }
  ; piTy = record
    { Πᴹ    = Π
    ; ƛᴹ_   = ƛ_
    ; appᴹ  = app
    ; []Πᴹ = λ {_} {_} {σ} {i} {A} {B} → cong (λ τ → Π ([ σ ] A) ([ τ ] B)) (↑=⁺ A σ)
            {- cong (λ τ → Π ([ σ ] A) ([ τ ] B))
                   (↑=⁺ A σ ∙ cong (π₁ idS ⨟ σ ,_) 
                                   (cong (λ p → tr (TmᴹFam toQIIRT) p (π₂ idS)) (uip refl (sym [⨟]))))
            -}
    ; []ƛᴹ  = λ {_} {_} {_} {A} {B} σ t 
            → []ƛeq σ t
    ; Πβᴹ   = Πβ
    ; Πηᴹ   = Πη
    }
  ; idTy = record
    { Idᴹ      = Id
    ; []Idᴹ   = refl
    ; reflᴹ    = refl
    ; []reflᴹ  = λ σ {a} t → sym ([]tm≡[]t (refl t) σ) ∙ []refl σ t
    ; reflectᴹ = reflect
    }
  }
  where open ≡-Reasoning
