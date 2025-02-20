open import Prelude
  
module SC+U+Pi+Id.QIIT.Properties where 

open import SC+U+Pi+Id.QIIT.Syntax

opaque 
  []tapp : (σ : Sub Γ Δ)
    → (A : Ty Δ i) (B : Ty (Δ , A) i) (t : Tm Δ (Π A B))
    → app (tr (Tm Γ) []Π ([ σ ]tm t)) ≡ [ σ ↑ A ]tm app t
  []tapp {Γ} σ A B t = begin
    app (tr (Tm Γ) []Π ([ σ ]tm t))
      ≡⟨ cong (λ z → app (tr (Tm Γ) []Π ([ σ ]tm z))) (sym Πη) ⟩
    app (tr (Tm Γ) []Π ([ σ ]tm (ƛ app t)))
      ≡⟨ cong app ([]ƛ σ (app t)) ⟩
    app (ƛ ([ σ ↑ A ]tm app t))
      ≡⟨ Πβ ⟩
    [ σ ↑ A ]tm app t
      ∎
    where open ≡-Reasoning

  π,
    : (σ : Sub Γ Δ) (t : Tm Γ ([ σ ] A))
    → _≡_ {_} {A = Σ (Sub Γ Δ) (λ σ → Tm Γ ([ σ ] A))}
    (π₁ (σ , t) , π₂ (σ , t))
    (σ , t)
  π, σ t = begin
    π₁ (σ , t) , π₂ (σ , t)
      ≡⟨ Σ-≡,≡→≡ (π₁, , π₂,) ⟩
    σ , t
      ∎
    where open ≡-Reasoning

  π⨟
    : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
    → _≡_ {A = Σ (Sub Γ Θ) (λ σ → Tm Γ ([ σ ] A))}
      (π₁ (σ ⨟ τ) , π₂ (σ ⨟ τ))
      (σ ⨟ π₁ τ , tr (Tm Γ) (sym $ [⨟]) ([ σ ]tm (π₂ τ)))
  π⨟ {Γ} {Δ} {Θ} {i} {A} σ τ = begin
    π₁ (σ ⨟ τ) , π₂ (σ ⨟ τ)
      ≡⟨ apΣ (λ σ → Tm Γ ([ σ ] A)) (λ τ → π₁ (σ ⨟ τ)) (apdΣ (λ τ → π₂ (σ ⨟ τ)) η,) ⟩
    π₁ (σ ⨟ (π₁ τ , π₂ τ)) , π₂ (σ ⨟ (π₁ τ , π₂ τ))
      ≡⟨ apΣ (λ σ → Tm Γ ([ σ ] A)) π₁ (apdΣ π₂ ⨟,) ⟩
    let t = tr (Tm Γ) (sym $ [⨟]) ([ σ ]tm (π₂ τ)) in
    π₁ (σ ⨟ π₁ τ , t) , π₂ (σ ⨟ π₁ τ , t)
      ≡⟨ π, (σ ⨟ π₁ τ) t ⟩
    σ ⨟ π₁ τ , t
      ∎
    where open ≡-Reasoning

-- derived computation rules on composition
  π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
  π₁⨟ σ τ = Σ-≡,≡←≡ (π⨟ σ τ) .proj₁

  π₂⨟ : (σ : Sub Γ Δ) {A : Ty Θ i} (τ : Sub Δ (Θ , A))
    → _≡_ {_} {∃ (Tm Γ)}
    ([ π₁ (σ ⨟ τ) ] A , π₂ (σ ⨟ τ))
    ([ σ ] [ π₁ τ ] A , [ σ ]tm (π₂ τ))
  π₂⨟ {Γ} σ {A} τ = begin
    [ π₁ (σ ⨟ τ) ] A , π₂ (σ ⨟ τ)
      ≡⟨ apΣ (Tm Γ) ([_] A) (π⨟ σ τ) ⟩
    [ σ ⨟ π₁ τ ] A , tr (Tm Γ) (sym [⨟]) ([ σ ]tm π₂ τ)
      ≡⟨ (sym $ lift (Tm Γ) ([ σ ]tm π₂ τ) (sym [⨟])) ⟩ 
    [ σ ] [ π₁ τ ] A , [ σ ]tm (π₂ τ)
      ∎
    where open ≡-Reasoning

  
  ⨟π₁id  : (σ : Sub Γ (Δ , A)) → π₁ σ ≡ σ ⨟ π₁ idS
  ⨟π₁id σ = begin
    π₁ σ         ≡⟨ sym $ cong π₁ (σ ⨟idS) ⟩
    π₁ (σ ⨟ idS) ≡⟨ π₁⨟ σ idS ⟩
    σ ⨟ π₁ idS   ∎
    where open ≡-Reasoning

  ⨟π₂id : (σ : Sub Γ (Δ , A))
    → _≡_ {_} {∃ (Tm Γ)}
    ([ π₁ σ ] A , π₂ σ)
    ([ σ ] [ wk ] A , [ σ ]tm vz)
  ⨟π₂id {Γ} {Δ} {i} {A} σ = begin
    [ π₁ σ ] A , π₂ σ
      ≡⟨ apΣ (Tm Γ) (λ σ → [ π₁ σ ] A) (apdΣ π₂ (sym $ σ ⨟idS)) ⟩
    [ π₁ (σ ⨟ idS) ] A , π₂ (σ ⨟ idS)
      ≡⟨ π₂⨟ σ idS ⟩
    [ σ ] [ wk ] A , [ σ ]tm vz
      ∎
    where open ≡-Reasoning

  ⁺⨟wk : (σ : Sub Γ Δ) {A : Ty Δ i} → (σ ↑ A) ⨟ wk ≡ wk ⨟ σ
  ⁺⨟wk {Γ} {Δ} σ {A} = begin
    (σ ↑ A) ⨟ π₁ idS               ≡⟨ (sym $ ⨟π₁id (σ ↑ A)) ⟩
    π₁ (σ ↑ A)                     ≡⟨⟩
    π₁ (π₁ idS ⨟ σ , tr (Tm (Γ , [ σ ] A)) (sym [⨟]) vz) ≡⟨ π₁, ⟩
    π₁ idS ⨟ σ ∎
    where open ≡-Reasoning

  [↑][wk]=[wk][]
    : [ σ ↑ A ] [ wk ] A ≡ [ wk ] [ σ ] A
  [↑][wk]=[wk][] {σ = σ} {A = A} = sym [⨟] ∙ cong ([_] A) (⁺⨟wk σ) ∙ [⨟]

  [⁺]vz : (σ : Sub Γ Δ) (A : Ty Δ i)
    → [ σ ↑ A ]tm (π₂ idS)
    ≅ π₂ {A = [ σ ] A} idS
  [⁺]vz {Γ} {Δ} σ A = begin
    [ σ ↑ A ]tm (π₂ idS)
      ≅⟨ ≡-to-≅ $ Σ-≡,≡←≡ (π₂⨟ (σ ↑ A) idS) .proj₂ ⟨
    tr (Tm (Γ , [ σ ] A)) (Σ-≡,≡←≡ (π₂⨟ (σ ↑ A) idS) .proj₁) (π₂ ((σ ↑ A) ⨟ idS))
      ≅⟨ tr≅ (Tm (Γ , [ σ ] A)) (Σ-≡,≡←≡ (π₂⨟ (σ ↑ A) idS) .proj₁) _ ⟩
    π₂ ((σ ↑ A) ⨟ idS)
      ≅⟨ hcong π₂ (≡-to-≅ $ (σ ↑ A) ⨟idS) ⟩
    π₂ (π₁ idS ⨟ σ , tr (Tm (Γ , [ σ ] A)) (sym [⨟]) (π₂ idS))
      ≅⟨ tr≅ (λ σ' → Tm (Γ , [ σ ] A) ([ σ' ] A)) π₁, _ ⟨
    tr (λ σ' → Tm (Γ , [ σ ] A) ([ σ' ] A)) π₁, _
      ≅⟨ ≡-to-≅ π₂, ⟩
    tr (Tm (Γ , [ σ ] A)) (sym [⨟]) (π₂ idS)
      ≅⟨ tr≅ (Tm (Γ , [ σ ] A)) (sym [⨟]) _ ⟩
    π₂ idS
      ∎
    where open ≅-Reasoning

  id⁺
    : (Γ : Ctx) (A : Ty Γ i)
    → tr (λ B → Sub (Γ , B) (Γ , A)) [idS] (idS {Γ} ↑ A)
    ≡ idS {Γ , A}
  id⁺ Γ A = begin
      let vz' = tr (Tm _) (sym [⨟]) vz in
    tr (λ B → Sub (Γ , B) (Γ , A)) [idS]
      (wk ⨟ idS , vz')
      ≡⟨ tr-nat (λ B → Tm (Γ , B) ([ wk ⨟ idS ] A)) (λ _ t → wk ⨟ idS , t) [idS] ⟩
    wk ⨟ idS , tr (λ B → Tm (Γ , B) ([ wk ⨟ idS ] A)) [idS] vz'
      ≡⟨ apd₂ (λ σ t → _,_ σ {A} t) (wk ⨟idS) eq ⟩
    wk , π₂ idS
      ≡⟨ sym $ η, ⟩
    idS
      ∎
    where
      open ≡-Reasoning

      vz≅ : π₂ {Γ , [ idS ] A} idS ≅ π₂ {Γ , A} idS
      vz≅ = HEq.cong (λ A → π₂ {Γ , A} idS) (≡-to-≅ [idS])

      eq : tr (λ σ → Tm (Γ , A) ([ σ ] A)) (wk ⨟idS)
              (tr (λ B → Tm (Γ , B) ([ wk ⨟ idS ] A)) [idS]
                  (tr (Tm (Γ , [ idS ] A)) (sym [⨟]) vz))
         ≡ vz
      eq = ≅-to-≡ $
        HEq.trans (tr≅ (λ σ → Tm (Γ , A) ([ σ ] A)) (wk ⨟idS)
                       (tr (λ B → Tm (Γ , B) ([ wk ⨟ idS ] A)) [idS]
                           (tr (Tm (Γ , [ idS ] A)) (sym [⨟]) vz)))
       (HEq.trans (tr≅ (λ B → Tm (Γ , B) ([ wk ⨟ idS ] A)) [idS]
                       (tr (Tm (Γ , [ idS ] A)) (sym [⨟]) vz))
       (HEq.trans (tr≅ (Tm (Γ , [ idS ] A)) (sym [⨟]) vz)
                   vz≅))

  ⨟⁺
    : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (B : Ty Θ i)
    → tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] ((σ ⨟ τ) ↑ B) ≡ (σ ↑ ([ τ ] B))  ⨟ (τ ↑ B)
  ⨟⁺ {Γ} {Δ} {Θ} {i} σ τ B = ≅-to-≡ $ begin
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]
       (wk ⨟ (σ ⨟ τ) , tr (Tm (Γ , [ σ ⨟ τ ] B)) (sym [⨟]) vz)
      ≡⟨ tr-nat (λ B' → Tm (Γ , B') ([ wk ⨟ (σ ⨟ τ) ] B)) (λ _ t' → wk ⨟ (σ ⨟ τ) , t') [⨟] ⟩
    wk ⨟ (σ ⨟ τ) ,
      tr (λ B' → Tm (Γ , B') ([ wk ⨟ (σ ⨟ τ) ] B)) [⨟]
         (tr (Tm (Γ , [ σ ⨟ τ ] B)) (sym [⨟]) vz)
      ≡⟨ eq ≡,≅ heq ⟩
    (σ ↑ ([ τ ] B)) ⨟ (wk ⨟ τ) ,
      tr (Tm (Γ , [ σ ] [ τ ] B)) (sym [⨟])
         ([ σ ↑ ([ τ ] B) ]tm tr (Tm (Δ , [ τ ] B)) (sym [⨟]) vz)
      ≡⟨ ⨟, ⟨
    (σ ↑ ([ τ ] B)) ⨟ (wk ⨟ τ , tr (Tm _) (sym [⨟]) vz)
      ∎
    where
      open ≅-Reasoning
      _≡,≅_
        : ∀{Γ Δ i}{A : Ty Δ i}
          {σ σ' : Sub Γ Δ}{t : Tm Γ ([ σ ] A)}{t' : Tm Γ ([ σ' ] A)}
        → σ ≡ σ' → t ≅ t'
        → _≡_ {A = Sub Γ (Δ , A)} (σ , t) (σ' , t')
      refl ≡,≅ eq = cong (_ ,_) (≅-to-≡ eq)

      eq : wk ⨟ (σ ⨟ τ) ≡ (σ ↑ ([ τ ] B)) ⨟ (wk ⨟ τ)
      eq = ≅-to-≡ $ begin
        wk ⨟ (σ ⨟ τ)
          ≡⟨ ⨟-assoc ⟩
        (wk ⨟ σ) ⨟ τ
          ≡⟨ cong (_⨟ τ) (⁺⨟wk σ) ⟨
        (σ ↑ ([ τ ] B)) ⨟ wk ⨟ τ
          ≡⟨ ⨟-assoc ⟨
        (σ ↑ ([ τ ] B)) ⨟ (wk ⨟ τ)
          ∎
      
      heq : tr (λ B' → Tm (Γ , B') ([ wk ⨟ (σ ⨟ τ) ] B)) [⨟]
               (tr (Tm (Γ , [ σ ⨟ τ ] B)) (sym [⨟]) vz)
          ≅ tr (Tm (Γ , [ σ ] [ τ ] B)) (sym [⨟])
               ([ σ ↑ ([ τ ] B) ]tm tr (Tm (Δ , [ τ ] B)) (sym [⨟]) vz)
      heq = begin
        tr (λ B' → Tm (Γ , B') ([ wk ⨟ (σ ⨟ τ) ] B)) [⨟]
           (tr (Tm (Γ , [ σ ⨟ τ ] B)) (sym [⨟]) vz)
          ≅⟨ tr≅ (λ B' → Tm (Γ , B') ([ wk ⨟ (σ ⨟ τ) ] B)) [⨟] _ ⟩
        tr (Tm (Γ , [ σ ⨟ τ ] B)) (sym [⨟]) vz
          ≅⟨ tr≅ (Tm (Γ , [ σ ⨟ τ ] B)) (sym [⨟]) _ ⟩
        π₂ {A = [ σ ⨟ τ ] B} idS
          ≅⟨ hcong (λ A → π₂ {A = A} idS) (≡-to-≅ [⨟]) ⟩
        π₂ {A = [ σ ] [ τ ] B} idS
          ≅⟨ [⁺]vz σ ([ τ ] B) ⟨
        [ σ ↑ ([ τ ] B) ]tm π₂ {A = [ τ ] B} idS -- : Tm (Δ , [ τ ] B) ([ wk ] [ τ ] B)
          ≅⟨ icong (Tm (Δ , [ τ ] B)) [⨟] ([ σ ↑ ([ τ ] B) ]tm_)
                    (tr≅ (Tm (Δ , [ τ ] B)) (sym [⨟]) _) ⟨
        [ σ ↑ ([ τ ] B) ]tm tr (Tm (Δ , [ τ ] B)) (sym [⨟]) vz
          ≅⟨ tr≅ (Tm (Γ , [ σ ] [ τ ] B)) (sym [⨟]) _ ⟨
        tr (Tm (Γ , [ σ ] [ τ ] B)) (sym [⨟])
           ([ σ ↑ ([ τ ] B) ]tm tr (Tm (Δ , [ τ ] B)) (sym [⨟]) vz)
          ∎

  π₁,⁺
    : tr (λ A → Sub (Γ , A) (Δ , B)) (cong ([_] B) π₁,) (π₁ (σ , t) ↑ B)
    ≡ σ ↑ B 
  π₁,⁺ {Γ} {Δ} {i} {B} {σ} {j} {C} {t} = begin
    tr (λ A → Sub (Γ , A) (Δ , B)) (cong ([_] B) π₁,)
    (π₁ (σ , t) ↑ B)
      ≡⟨ tr-cong π₁, ⟨
    tr (λ σ → Sub (Γ , [ σ ] B) (Δ , B)) π₁,
    (π₁ (σ , t) ↑ B)
      ≡⟨ apd (λ σ → σ ↑ B) π₁, ⟩
    σ ↑ B
      ∎
    where open ≡-Reasoning

  π₁⨟⁺
    : tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ) ∙ [⨟])
      ((π₁ (σ ⨟ τ)) ↑ B)
    ≡ (σ ↑ ([ π₁ τ ] B)) ⨟ (π₁ τ) ↑ B
  π₁⨟⁺ {Γ} {Θ} {i} {B} {Δ} {σ} {j} {A} {τ} = begin
    tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ) ∙ [⨟])
      ((π₁ (σ ⨟ τ)) ↑ B)
      ≡⟨  tr² (cong ([_] B) (π₁⨟ σ τ)) ⟨
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] (tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ))
      ((π₁ (σ ⨟ τ)) ↑ B) )
      ≡⟨ cong (tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]) (tr-cong (π₁⨟ σ τ)) ⟨
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] (tr (λ σ → Sub (Γ , [ σ ] B) (Θ , B)) (π₁⨟ σ τ)
      ((π₁ (σ ⨟ τ)) ↑ B)) 
      ≡⟨ cong (tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]) (apd (λ σ → σ ↑ B) (π₁⨟ σ τ)) ⟩
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] ((σ ⨟ π₁ τ) ↑ B)
      ≡⟨ ⨟⁺ _ _ _ ⟩
    (σ ↑ ([ π₁ τ ] B)) ⨟ ((π₁ τ) ↑ B)
      ∎ 
    where open ≡-Reasoning
