open import Prelude
-- copy and modify from Theory
module SC+U+Pi+Id.Translation.Syntax.toQIIRT where

open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties
open import SC+U+Pi+Id.Recursion.Rec

open Recursor

private
  []ƛeq : {A : Ty Δ i}{B : Ty (Δ , A) i}(σ : Sub Γ Δ)(t : Tm (Δ , A) B)
        → tr (Tm Γ) (cong (λ τ → Π ([ σ ] A) ([ τ ] B))
                          (↑=⁺ A σ ∙ cong (π₁ idS ⨟ σ ,_)
                                          (cong (λ p → tr (Tm (Γ , [ σ ] A)) p (π₂ {A = [ σ ] A} idS))
                                                (uip refl (sym $ [⨟] {A = A})))))
                    ([ σ ]t (ƛ t))
        ≡ ƛ ([ π₁ {A = [ σ ] A} idS ⨟ σ , tr (Tm (Γ , [ σ ] A)) (sym $ [⨟] {σ = π₁ idS} {τ = σ} {A = A}) (π₂ idS) ]t t)
  []ƛeq {Δ} {i} {Γ} {A = A} {B} σ t = sym $ ≅-to-≡ $ begin
    ƛ ([ π₁ {A = [ σ ] A} idS ⨟ σ ,
            tr (Tm (Γ , [ σ ] A)) (sym $ [⨟] {σ = π₁ idS} {τ = σ} {A = A}) (π₂ idS) ]t t)
      ≅⟨ hcong (λ p → ƛ ([ π₁ {A = [ σ ] A} idS ⨟ σ , tr (Tm (Γ , [ σ ] A)) p (π₂ idS) ]t t))
               (≡-to-≅ $ uip (sym [⨟]) refl) ⟩
    ƛ ([ π₁ idS ⨟ σ , π₂ idS ]tm t)
      ≅⟨ hcong (λ σ' → ƛ ([ σ' ]tm t)) (≡-to-≅ (sym $ ↑=⁺ A σ)) ⟩
    ƛ ([ σ ↑ A ]tm t)
      ≅⟨ ≡-to-≅ $ sym $ []ƛ σ t ⟩
    [ σ ]tm (ƛ t)
      ≅⟨ ≡-to-≅ $ []tm≡[]t (ƛ t) σ ⟩
    [ σ ]t (ƛ t)
      ≅⟨ tr≅ (Tm Γ)
                (cong (λ τ → Π ([ σ ] A) ([ τ ] B))
                      (↑=⁺ A σ ∙ cong (_,_ (π₁ idS ⨟ σ))
                                      (cong (λ p → tr (Tm (Γ , [ σ ] A)) p (π₂ idS))
                                            (uip refl (sym $ [⨟] {σ = π₁ idS} {τ = σ} {A = A})))))
                ([ σ ]t (ƛ t)) ⟨
    tr (Tm Γ) _ ([ σ ]t (ƛ t))
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
    { C₁ = record
      { [_]ᴹ_       = [_]_
      ; ∅ᶜᴹ         = ∅
      ; _,ᶜᴹ_       = _,_
      ; ∅ˢᴹ         = ∅
      ; _,ˢᴹ_       = _,_
      ; idSᴹ        = idS
      ; _⨟ᴹ_        = _⨟_
      ; π₁ᴹ         = π₁
      ; [idSᴹ]      = [id]
      ; [⨟ᴹ]ᴹ       = λ {_} {_} {_} {_} {σ} {τ} {A} → [⨟] {_} {_} {σ} {_} {τ} {_} {A}
      ; π₂ᴹ         = π₂
      ; [_]tmᴹ_     = [_]t_
      }
    ; C₂ = record
      { _⨟ᴹidSᴹ     = _⨟idS
      ; idSᴹ⨟ᴹ_     = idS⨟_
      ; ⨟ᴹ-assoc    = ⨟-assoc
      ; π₁ᴹ,ˢᴹ      = π₁,
      ; ⨟ᴹ,ˢᴹ       = λ {_} {Γ} {Δ} {Θ} {A} {σ} {τ} {t}
                    → ⨟, ∙ cong (σ ⨟ τ ,_)
                                ([]tm≡[]t t σ 
                                ∙ sym (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t t)) (uip (sym [⨟]) refl)))
      ; η∅ˢᴹ        = η∅
      ; η,ˢᴹ        = η,
      ; [idSᴹ]tmᴹ   = λ {_} {_} {_} {t} → cong (λ p → tr (TmᴹFam toQIIRT) p t) (uip [id] refl)
      ; [⨟ᴹ]tmᴹ     = λ {_} {_} {σ} {_} {τ} {_} {_} {t}
                    → cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t [ τ ]t t)) (uip [⨟] refl)
      ; π₂ᴹ,ˢᴹ      = λ {_} {_} {_} {A} {σ} {t} 
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
    }
  ; univ = record
    { Uᴹ       = U
    ; Elᴹ      = El
    ; Liftᴹ    = Lift
    ; cᴹ       = c
    ; mkᴹ      = mk
    ; unᴹ      = un
    ; []ᴹUᴹ    = λ {_} {_} {σ} {i} → refl
    ; []ᴹElᴹ   = λ σ u → refl
    ; []ᴹLiftᴹ = λ {_} {_} {σ} {i} {A} → refl
    ; []tᴹcᴹ   = λ σ A → sym ([]tm≡[]t (c A) σ) ∙ []tc σ A
    ; []mkᴹ    = λ σ t → -- cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t mk t)) (uip []Lift refl)
                       sym ([]tm≡[]t (mk t) σ)
                       ∙ []mk σ t
    ; []unᴹ    = λ σ A t → sym ([]tm≡[]t (un t) σ)
                         ∙ []un σ A t
                         ∙ cong un ([]tm≡[]t t σ) -- ∙ cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t t)) (uip refl []Lift))
    ; Uᴹβ      = Uβ
    ; Uᴹη      = Uη
    ; Liftᴹβ   = Liftβ
    ; Liftᴹη   = Liftη
    }
  ; piTy = record
    { Πᴹ    = Π
    ; ƛᴹ_   = ƛ_
    ; appᴹ  = app
    ; []ᴹΠᴹ = λ {_} {_} {σ} {i} {A} {B}
            → cong (λ τ → Π ([ σ ] A) ([ τ ] B))
                   (↑=⁺ A σ ∙ cong (π₁ idS ⨟ σ ,_) 
                                   (cong (λ p → tr (TmᴹFam toQIIRT) p (π₂ idS)) (uip refl (sym [⨟]))))
    ; []ƛᴹ  = λ {_} {_} {_} {A} {B} σ t 
            → []ƛeq σ t
    ; Πβᴹ   = Πβ
    ; Πηᴹ   = Πη
    }
  ; idTy = record
    { Idᴹ      = Id
    ; []ᴹIdᴹ   = refl
             {- λ {_} {_} {i} {σ} {a} {t} {u}
               → cong₃ Id
                       (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) ? ) -- (uip refl []U))
                       (tr-cong {P = TmᴹFam toQIIRT} (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) (uip refl []U))
                       ∙ cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t t))
                              (uip (cong El (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) (uip refl []U)))
                                   (cong El (sym ((cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) (uip []U refl)))))))
                       (tr-cong {P = TmᴹFam toQIIRT} (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) (uip refl []U))
                       ∙ cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t u))
                              (uip (cong El (cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) (uip refl []U)))
                                   (cong El (sym ((cong (λ p → tr (TmᴹFam toQIIRT) p ([ σ ]t a)) (uip []U refl)))))))
                                   -}
    ; reflᴹ    = refl
    ; []reflᴹ  = λ σ {a} t → sym ([]tm≡[]t (refl t) σ) ∙ []refl σ t
    ; reflectᴹ = reflect
    }
  }
  where open ≡-Reasoning
