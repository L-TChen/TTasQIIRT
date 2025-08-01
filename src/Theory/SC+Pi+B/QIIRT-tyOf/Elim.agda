module Theory.SC+Pi+B.QIIRT-tyOf.Elim where

open import Prelude

open import Theory.SC+Pi+B.QIIRT-tyOf.Syntax

record Motive (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctxᴬ
      : (Γ : Ctx)
      → Set ℓ₁
    Tyᴬ
      : Ctxᴬ Γ → Ty Γ
      → Set ℓ₂
    Subᴬ
      : (Γᴹ : Ctxᴬ Γ) (Δᴹ : Ctxᴬ Δ) → Sub Γ Δ
      → Set ℓ₃
    Tmᴬ
      : Ctxᴬ Γ → Tm Γ
      → Set ℓ₄
    tyOfᴬ
      : {Γᴹ : Ctxᴬ Γ} → Tmᴬ Γᴹ t
      → Tyᴬ Γᴹ (tyOf t)
    
    Tyᴬ-is-set
      : {Γᴹ : Ctxᴬ Γ} → isSet (Tyᴬ Γᴹ A)

  variable
    Γᴹ Δᴹ Θᴹ Ξᴹ : Ctxᴬ Γ
    Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴬ  Γᴹ A
    σᴹ τᴹ γᴹ    : Subᴬ Γᴹ Δᴹ σ
    tᴹ uᴹ vᴹ    : Tmᴬ  Γᴹ t

-- Recursor

module _ (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motive mot

  record SCᴹ : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      ∅ᴹ
        : Ctxᴬ ∅
      _,ᴹ_
        : (Γᴹ : Ctxᴬ Γ)(Aᴹ : Tyᴬ Γᴹ A)
        → Ctxᴬ (Γ , A)
      _[_]Tᴹ
        : (Aᴹ : Tyᴬ Δᴹ A)(σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → Tyᴬ Γᴹ (A [ σ ])
      _[_]tᴹ
        : (tᴹ : Tmᴬ Δᴹ t)(σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → Tmᴬ Γᴹ (t [ σ ])
      tyOf[]ᴹ
        : tyOfᴬ (tᴹ [ σᴹ ]tᴹ) ≡ (tyOfᴬ tᴹ) [ σᴹ ]Tᴹ
      ∅Sᴹ
        : Subᴬ Γᴹ ∅ᴹ ∅
      _,ᴹ_∶[_,_]
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) {Aᴹ : Tyᴬ Δᴹ A} (tᴹ : Tmᴬ Γᴹ t)
        → (p : tyOf t ≡ A [ σ ])
        → tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] (Aᴹ [ σᴹ ]Tᴹ)
        → Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) (σ , t ∶[ p ])
      idSᴹ
        : Subᴬ Γᴹ Γᴹ idS
      _∘ᴹ_
        : Subᴬ Δᴹ Θᴹ τ → Subᴬ Γᴹ Δᴹ σ
        → Subᴬ Γᴹ Θᴹ (τ ∘ σ)
      π₁ᴹ
        : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ
        → Subᴬ Γᴹ Δᴹ (π₁ σ)
      π₂ᴹ
        : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ
        → Tmᴬ Γᴹ (π₂ σ)
      tyOfπ₂ᴹ
        : tyOfᴬ (π₂ᴹ σᴹ) ≡ Aᴹ [ π₁ᴹ σᴹ ]Tᴹ
      idS∘ᴹ_
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → idSᴹ ∘ᴹ σᴹ
        ≡[ i ⊢ Subᴬ Γᴹ Δᴹ ((idS∘ σ) i) ] σᴹ
        -- [TODO] Justify the usage of transport in the eliminator
      _∘idSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → σᴹ ∘ᴹ idSᴹ
        ≡[ i ⊢ Subᴬ Γᴹ Δᴹ ((σ ∘idS) i) ] σᴹ
      assocSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (τᴹ : Subᴬ Δᴹ Θᴹ τ) (γᴹ : Subᴬ Θᴹ Ξᴹ γ)
        → (γᴹ ∘ᴹ τᴹ) ∘ᴹ σᴹ
        ≡[ i ⊢ Subᴬ Γᴹ Ξᴹ (assocS σ τ γ i) ]
           γᴹ ∘ᴹ (τᴹ ∘ᴹ σᴹ)
      ,∘ᴹ
        : (σᴹ : Subᴬ Δᴹ Θᴹ σ) (tᴹ : Tmᴬ Δᴹ t) (τᴹ : Subᴬ Γᴹ Δᴹ τ)
          (p : tyOf t ≡ A [ σ ]) (pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Δᴹ (p i) ] Aᴹ [ σᴹ ]Tᴹ)
          (q : tyOf (t [ τ ]) ≡ A [ σ ∘ τ ]) (qᴹ : tyOfᴬ (tᴹ [ τᴹ ]tᴹ) ≡[ i ⊢ Tyᴬ Γᴹ (q i) ] (Aᴹ [ σᴹ ∘ᴹ τᴹ ]Tᴹ))
        → (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ]) ∘ᴹ τᴹ
        ≡[ i ⊢ Subᴬ Γᴹ (Θᴹ ,ᴹ Aᴹ) (,∘ σ t τ p q i) ]
          ((σᴹ ∘ᴹ τᴹ) ,ᴹ tᴹ [ τᴹ ]tᴹ ∶[ q , qᴹ ])
      ηπᴹ
        : (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ)
        → σᴹ
        ≡[ i ⊢ Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) (ηπ σ i) ]
          (π₁ᴹ σᴹ ,ᴹ π₂ᴹ σᴹ ∶[ refl , tyOfπ₂ᴹ ])
      η∅ᴹ
        : (σᴹ : Subᴬ Γᴹ ∅ᴹ σ)
        → σᴹ ≡[ i ⊢ Subᴬ Γᴹ ∅ᴹ (η∅ σ i) ] ∅Sᴹ
      βπ₁ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (tᴹ : Tmᴬ Γᴹ t)
        → (p : tyOf t ≡ A [ σ ]) (pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Aᴹ [ σᴹ ]Tᴹ)
        → π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ])
        ≡[ i ⊢ Subᴬ Γᴹ Δᴹ (βπ₁ σ t p i) ]
          σᴹ
      βπ₂ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (tᴹ : Tmᴬ Γᴹ t)
        → (p : tyOf t ≡ A [ σ ]) (pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Aᴹ [ σᴹ ]Tᴹ)
        → (q : A [ π₁ (σ , t ∶[ p ]) ] ≡ tyOf t)
          (qᴹ : Aᴹ [ π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ]) ]Tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (q i) ] tyOfᴬ tᴹ)
        → π₂ᴹ (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ])
        ≡[ i ⊢ Tmᴬ Γᴹ (βπ₂ σ t p q i) ]
          tᴹ
      [idS]Tᴹ
        : (Aᴹ : Tyᴬ Γᴹ A)
        → Aᴹ
        ≡[ i ⊢ Tyᴬ Γᴹ ([idS]T {Γ} {A} i) ]
          Aᴹ [ idSᴹ ]Tᴹ
      [∘]Tᴹ
        : (Aᴹ : Tyᴬ Θᴹ A) (σᴹ : Subᴬ Γᴹ Δᴹ σ) (τᴹ : Subᴬ Δᴹ Θᴹ τ)
        → Aᴹ [ τᴹ ]Tᴹ [ σᴹ ]Tᴹ
        ≡[ i ⊢ Tyᴬ Γᴹ ([∘]T A σ τ i) ]
          Aᴹ [ τᴹ ∘ᴹ σᴹ ]Tᴹ
      [idS]tᴹ
        : (tᴹ : Tmᴬ Γᴹ t)
        → tᴹ
        ≡[ i ⊢ Tmᴬ Γᴹ ([idS]t t i) ]
          tᴹ [ idSᴹ ]tᴹ
      [∘]tᴹ
        : (tᴹ : Tmᴬ Θᴹ t) (σᴹ : Subᴬ Γᴹ Δᴹ σ) (τᴹ : Subᴬ Δᴹ Θᴹ τ)
        → tᴹ [ τᴹ ]tᴹ [ σᴹ ]tᴹ
        ≡[ i ⊢ Tmᴬ Γᴹ ([∘]t t σ τ i) ]
          tᴹ [ τᴹ ∘ᴹ σᴹ ]tᴹ
     --  tyOfπ₂idSᴹ
     --    : tyOfᴬ (π₂ᴹ {Aᴹ = Aᴹ [ σᴹ ]Tᴹ} idSᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
     -- [TODO] Do we need derived equations in recursor/eliminator?
     -- Derived equations are used to make the definition strictly positivie, not an issue for records.
     -- So, delete this for now to see if need it in an recorsor

    tyOfπ₂idSᴹ
      : {Δᴹ : Ctxᴬ Δ} {Aᴹ : Tyᴬ Δᴹ A} {σᴹ : Subᴬ Γᴹ Δᴹ σ}
      → tyOfᴬ (π₂ᴹ idSᴹ)
      ≡[ i ⊢ Tyᴬ (Γᴹ ,ᴹ (Aᴹ [ σᴹ ]Tᴹ)) (tyOfπ₂idS i) ]
        (Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ)
    tyOfπ₂idSᴹ {Aᴹ = Aᴹ} {σᴹ = σᴹ} = {!!}
    {-
      tyOfᴬ (π₂ᴹ idSᴹ)
        ≡⟨ tyOfπ₂ᴹ ⟩
      (Aᴹ [ σᴹ ]Tᴹ) [ π₁ᴹ idSᴹ ]Tᴹ
        ≡⟨ [∘]Tᴹ _ _ _ ⟩
      Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
         ∎
    -}

    _↑ᴹ_
      : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (Aᴹ : Tyᴬ Δᴹ A)
      → Subᴬ (Γᴹ ,ᴹ (Aᴹ [ σᴹ ]Tᴹ)) (Δᴹ ,ᴹ Aᴹ) (σ ↑ A)
    σᴹ ↑ᴹ Aᴹ = (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ tyOfπ₂idS , tyOfπ₂idSᴹ ]

  record Piᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open SCᴹ C

    field
      Πᴹ
        : (Aᴹ : Tyᴬ Γᴹ A) (Bᴹ : Tyᴬ (Γᴹ ,ᴹ Aᴹ) B)
        → Tyᴬ Γᴹ (Π A B)
      appᴹ
        : {Aᴹ : Tyᴬ Γᴹ A}{Bᴹ : Tyᴬ (Γᴹ ,ᴹ Aᴹ) B}
        → (tᴹ : Tmᴬ Γᴹ t)(p : tyOf t ≡ Π A B) → tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Πᴹ Aᴹ Bᴹ
        → Tmᴬ (Γᴹ ,ᴹ Aᴹ) (app t p)
      tyOfappᴹ
        : {Aᴹ : Tyᴬ Γᴹ A}{Bᴹ : Tyᴬ (Γᴹ ,ᴹ Aᴹ) B}{tᴹ : Tmᴬ Γᴹ t}
        → (p : tyOf t ≡ Π A B)(pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Πᴹ Aᴹ Bᴹ)
        → tyOfᴬ (appᴹ {Bᴹ = Bᴹ} tᴹ p pᴹ) ≡ Bᴹ
      absᴹ
        : (tᴹ : Tmᴬ (Γᴹ ,ᴹ Aᴹ) t)
        → Tmᴬ Γᴹ (abs t)
      tyOfabsᴹ
        : {Aᴹ : Tyᴬ Γᴹ A}{tᴹ : Tmᴬ (Γᴹ ,ᴹ Aᴹ) t}
        → tyOfᴬ (absᴹ tᴹ) ≡ Πᴹ Aᴹ (tyOfᴬ tᴹ)
      Π[]ᴹ
        : {Aᴹ : Tyᴬ Γᴹ A}{Bᴹ : Tyᴬ (Γᴹ ,ᴹ Aᴹ) B}{σᴹ : Subᴬ Δᴹ Γᴹ σ}
        → (Πᴹ Aᴹ Bᴹ) [ σᴹ ]Tᴹ ≡[ i ⊢ Tyᴬ Δᴹ (Π[] {A = A} {B = B} {σ = σ} i) ] Πᴹ (Aᴹ [ σᴹ ]Tᴹ) (Bᴹ [ σᴹ ↑ᴹ Aᴹ ]Tᴹ)
      abs[]ᴹ
        : {σᴹ : Subᴬ Δᴹ Γᴹ σ}(tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ) t)
        → absᴹ tᴹ [ σᴹ ]tᴹ ≡[ i ⊢ Tmᴬ Δᴹ (abs[] {σ = σ} t i) ] absᴹ (tᴹ [ σᴹ ↑ᴹ Aᴹ ]tᴹ)
      Πβᴹ
        : {Aᴹ : Tyᴬ Γᴹ A}(tᴹ : Tmᴬ (Γᴹ ,ᴹ Aᴹ) t)
          (pᴹ : tyOfᴬ (absᴹ tᴹ) ≡[ i ⊢ Tyᴬ Γᴹ (tyOfabs {t = t} i) ] Πᴹ Aᴹ (tyOfᴬ tᴹ))
        → appᴹ (absᴹ tᴹ) (tyOfabs {t = t}) pᴹ ≡[ i ⊢ Tmᴬ (Γᴹ ,ᴹ Aᴹ) (Πβ t i) ] tᴹ
      Πηᴹ
        : {Aᴹ : Tyᴬ Γᴹ A}{Bᴹ : Tyᴬ (Γᴹ ,ᴹ Aᴹ) B}
        → (tᴹ : Tmᴬ Γᴹ t)(p : tyOf t ≡ Π A B)(pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Πᴹ Aᴹ Bᴹ)
        → absᴹ (appᴹ tᴹ p pᴹ) ≡[ i ⊢ Tmᴬ Γᴹ (Πη t p i) ] tᴹ

  record Boolᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open SCᴹ C

    field
      𝔹ᴹ
        : Tyᴬ Γᴹ 𝔹
      𝔹[]ᴹ
        : {Γᴹ : Ctxᴬ Γ}{Δᴹ : Ctxᴬ Δ}{σᴹ : Subᴬ Γᴹ Δᴹ σ}
        → 𝔹ᴹ {Γᴹ = Δᴹ} [ σᴹ ]Tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (𝔹[] {σ = σ} i) ] 𝔹ᴹ
      ttᴹ
        : Tmᴬ Γᴹ tt
      ffᴹ
        : Tmᴬ Γᴹ ff
      tyOfttᴹ
        : tyOfᴬ {Γᴹ = Γᴹ} ttᴹ ≡ 𝔹ᴹ
      tyOfffᴹ
        : tyOfᴬ {Γᴹ = Γᴹ} ffᴹ ≡ 𝔹ᴹ
      tt[]ᴹ
        : {σᴹ : Subᴬ Γᴹ Δᴹ σ}
        → ttᴹ [ σᴹ ]tᴹ ≡[ i ⊢ Tmᴬ Γᴹ (tt[] {σ = σ} i) ] ttᴹ 
      ff[]ᴹ
        : {σᴹ : Subᴬ Γᴹ Δᴹ σ}
        → ffᴹ [ σᴹ ]tᴹ ≡[ i ⊢ Tmᴬ Γᴹ (ff[] {σ = σ} i) ] ffᴹ

    𝔹[]₂ᴹ'
      : {τᴹ : Subᴬ (Γᴹ ,ᴹ 𝔹ᴹ) Δᴹ τ}
      → let p = (λ i → Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ) (𝔹[] {σ = π₁ idS} i)) ∙ (λ i → Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ) (𝔹[] {σ = τ} (~ i)))
        in tyOfᴬ (π₂ᴹ {Γᴹ = Γᴹ ,ᴹ 𝔹ᴹ} idSᴹ) ≡[ i ⊢ p i ] 𝔹ᴹ [ τᴹ ]Tᴹ
    𝔹[]₂ᴹ' {τᴹ = τᴹ} = tyOfπ₂ᴹ {σᴹ = idSᴹ} {𝔹ᴹ} ◁ compPathP (𝔹[]ᴹ {σᴹ = π₁ᴹ idSᴹ}) (symP (𝔹[]ᴹ {σᴹ = τᴹ}))

    𝔹[]₂ᴹ
      : {τᴹ : Subᴬ (Γᴹ ,ᴹ 𝔹ᴹ) Δᴹ τ}
      → tyOfᴬ (π₂ᴹ {Γᴹ = Γᴹ ,ᴹ 𝔹ᴹ} idSᴹ) ≡[ i ⊢ Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ) (𝔹[]₂ {τ = τ} i) ] 𝔹ᴹ [ τᴹ ]Tᴹ
    𝔹[]₂ᴹ {Γᴹ = Γᴹ} {τᴹ = τᴹ} = {!   !}
    
    _↑𝔹ᴹ
      : (σᴹ : Subᴬ Γᴹ Δᴹ σ)
      → Subᴬ (Γᴹ ,ᴹ 𝔹ᴹ) (Δᴹ ,ᴹ 𝔹ᴹ) (σ ↑𝔹)
    σᴹ ↑𝔹ᴹ =
      (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ 𝔹[]₂ , 𝔹[]₂ᴹ {τᴹ = σᴹ ∘ᴹ π₁ᴹ idSᴹ} ] 

--     field
--       elim𝔹ᴹ
--         : (P : Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ)) (tᴹ uᴹ : Tmᴬ Γᴹ)
--         → tyOfᴬ tᴹ ≡ (P [ idSᴹ ,ᴹ ttᴹ ∶[ tyOfttᴹ ] ]Tᴹ)
--         → tyOfᴬ uᴹ ≡ (P [ idSᴹ ,ᴹ ffᴹ ∶[ tyOfffᴹ ] ]Tᴹ)
--         → (bᴹ : Tmᴬ Γᴹ) → tyOfᴬ bᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
--         → Tmᴬ Γᴹ
--       elim𝔹[]ᴹ
--         : (P : Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ)) (tᴹ uᴹ : Tmᴬ Γᴹ) (pt : tyOfᴬ tᴹ ≡ _) (pu : tyOfᴬ uᴹ ≡ _) → (bᴹ : Tmᴬ Γᴹ) (pb : tyOfᴬ bᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ)
--         → (pt₂ : tyOfᴬ (tᴹ [ σᴹ ]tᴹ) ≡ P [ σᴹ ↑𝔹ᴹ ]Tᴹ [ idSᴹ ,ᴹ ttᴹ ∶[ tyOfttᴹ ] ]Tᴹ)
--         → (pu₂ : tyOfᴬ (uᴹ [ σᴹ ]tᴹ) ≡ P [ σᴹ ↑𝔹ᴹ ]Tᴹ [ idSᴹ ,ᴹ ffᴹ ∶[ tyOfffᴹ ] ]Tᴹ)
--         → (pb₂ : tyOfᴬ (bᴹ [ σᴹ ]tᴹ) ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ)
--         → (P [ idSᴹ ,ᴹ bᴹ ∶[ pb ] ]Tᴹ [ σᴹ ]Tᴹ) ≡ (P [ (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ 𝔹[]₂ᴹ ] ]Tᴹ [ idSᴹ ,ᴹ bᴹ [ σᴹ ]tᴹ ∶[ pb₂ ] ]Tᴹ)
--         → (elim𝔹ᴹ P tᴹ uᴹ pt pu bᴹ pb) [ σᴹ ]tᴹ
--         ≡ elim𝔹ᴹ (P [ σᴹ ↑𝔹ᴹ ]Tᴹ) (tᴹ [ σᴹ ]tᴹ) (uᴹ [ σᴹ ]tᴹ) pt₂ pu₂ (bᴹ [ σᴹ ]tᴹ) pb₂

module _
  (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (SCᵐ : SCᴹ mot) -- (Boolᵐ : Boolᴹ mot SCᵐ) (Univᵐ : Univᴹ mot SCᵐ) (Piᵐ : Piᴹ mot SCᵐ)
  where

  open Motive mot
  open SCᴹ SCᵐ
--   open Boolᴹ Boolᵐ
--   open Univᴹ Univᵐ
--   open Piᴹ Piᵐ

  elimCtx  : (Γ : Ctx) → Ctxᴬ Γ
  elimTy   : (A : Ty Γ) → Tyᴬ (elimCtx Γ) A
  elimSub  : (σ : Sub Γ Δ) → Subᴬ (elimCtx Γ) (elimCtx Δ) σ
  elimTm   : (t : Tm Γ) → Tmᴬ (elimCtx Γ) t
  elimTyOf : {!!} -- {Γ : Ctx}{A : Ty Γ} → (t : Tm Γ) → tyOf t ≡ A → tyOfᴬ (elimTm t) ≡ elimTy A

  elimCtx ∅       = ∅ᴹ
  elimCtx (Γ , A) = elimCtx Γ ,ᴹ elimTy A

  elimTy (A [ σ ]) = {!!}
  elimTy (Π A B) = {!!}
  elimTy 𝔹 = {!!}
  elimTy ([idS]T i) = {!!}
  elimTy ([∘]T A σ τ i) = {!!}
  elimTy (Π[] i) = {!!}
  elimTy (𝔹[] i) = {!!}
  elimTy (𝔹[]₂ i) = {!!}
  elimTy (Ty-is-set A A₁ x y i i₁) = {!!}

  elimSub ∅              = ∅Sᴹ
  elimSub (σ , t ∶[ p ]) = elimSub σ ,ᴹ elimTm t ∶[ p , {!!} ]
  elimSub idS            = idSᴹ
  elimSub (τ ∘ σ)        = elimSub τ ∘ᴹ elimSub σ
  elimSub (π₁ σ)         = π₁ᴹ (elimSub σ)
  elimSub (βπ₁ σ t p i)  = {!!}
  elimSub ((idS∘ σ) i)   = {!!}
  elimSub ((σ ∘idS) i)   = {!!}
  elimSub (assocS σ σ₁ σ₂ i) = {!!}
  elimSub (,∘ σ t σ₁ p q i) = {!!}
  elimSub (η∅ σ i) = {!!}
  elimSub (ηπ σ i) = {!!}

  elimTm t  = {!!}
