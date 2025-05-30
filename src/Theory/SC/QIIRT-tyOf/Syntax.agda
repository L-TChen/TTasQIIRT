{-# OPTIONS --with-K #-}
-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude
  hiding (_,_)

module Theory.SC.QIIRT-tyOf.Syntax where
  
module Foo where
  module _ where -- delimit the scope of forward declarations
    infixl 8  _[_] _[_]T _[_]t
    infixr 10 _∘_
    infixl 4  _,_ _,_∶[_]

    data Ctx : Set
    data Sub : (Γ Δ : Ctx) → Set
    data Ty  : Ctx → Set
    data Tm  : (Γ : Ctx) → Set

    postulate
      tyOf
        : ∀ {Γ} → Tm Γ → Ty Γ

    variable
        Γ Δ Θ Ξ : Ctx
        A B C : Ty Γ
        t u   : Tm Γ
        σ τ δ : Sub Γ Δ

    -- Substitution calculus
    ∅
      : Ctx
    _,_
      : (Γ : Ctx)(A : Ty Γ)
      → Ctx
    _[_]T
      : (A : Ty Δ)(σ : Sub Γ Δ)
      → Ty Γ
    _[_]t
      : (A : Tm Δ)(σ : Sub Γ Δ)
      → Tm Γ
    ∅S
      : Sub Γ ∅
    _,_∶[_]
      : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≣ A [ σ ]T
      → Sub Γ (Δ , A)
    idS
      : Sub Γ Γ
    _∘_
      : Sub Δ Θ → Sub Γ Δ
      → Sub Γ Θ
    π₁
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    π₂
      : Sub Γ (Δ , A)
      → Tm Γ

    postulate
      tyOfπ₂ -- should be definitional after the datatype declaration
        : (σ : Sub Γ (Δ , A))
        → tyOf (π₂ σ) ≣ A [ π₁ σ ]T
      {-# REWRITE tyOfπ₂ #-}
    tyOfπ₂idS
      : tyOf (π₂ idS) ≣ A [ σ ∘ π₁ idS ]T
    
    _↑_
      : (σ : Sub Γ Δ) (A : Ty Δ)
      → Sub (Γ , A [ σ ]T) (Δ , A)
    σ ↑ A = σ ∘ π₁ idS , π₂ idS ∶[ tyOfπ₂idS ]

    idS∘_
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS
      : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (γ : Sub Θ Ξ)
      → (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ)
    ,∘
      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≣ A [ σ ]T)
        (q : tyOf (t [ τ ]t) ≣ A [ σ ∘ τ ]T)
      → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ q ])
    ηπ
      : (σ : Sub Γ (Δ , A))
      → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ])
    η∅
      : (σ : Sub Γ ∅)
      → σ ≡ ∅S
    βπ₁
      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≣ A [ σ ]T)
      → π₁ (σ , t ∶[ p ]) ≡ σ
    βπ₂
      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≣ A [ σ ]T)
      → (q : tyOf t ≣ A [ π₁ (σ , t ∶[ p ]) ]T)
      → π₂ (σ , t ∶[ p ]) ≡ t
    [idS]T
      : A ≡ A [ idS ]T
    [∘]T
      : (A : Ty Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
      → A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
    [idS]t
      : (t : Tm Γ)
      → t ≡ t [ idS ]t
    [∘]t
      : (t : Tm Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
      → t [ τ ]t [ σ ]t ≡ t [ τ ∘ σ ]t

    -- Empty universe
    U
      : Ty Γ
    U[]
      : U [ σ ]T ≡ U
    El
      : (u : Tm Γ) (p : tyOf u ≣ U)
      → Ty Γ
    El[]
      : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≣ U) (q : tyOf (u [ τ ]t) ≣ U)
      → (El u p) [ τ ]T ≡ El (u [ τ ]t) q

--     -- the following is the actual constructors in Agda
--     data Ctx where
--       ∅' : Ctx 
--       _,'_ : (Γ : Ctx) (A : Ty Γ) → Ctx
      
--     data Ty where
--       _[_] : (A : Ty Δ) (σ : Sub Γ Δ)
--         → Ty Γ
--       [idS]T'
--         : A ≡ A [ idS ]
--       [∘]T'
--         : (A : Ty Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
--         → A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
--       U'
--         : Ty Γ
--       U[]'
--         : U [ σ ]T ≡ U
--       El'
--         : (u : Tm Γ) (p : tyOf u ≣ U)
--         → Ty Γ
--       El[]'
--         : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≣ U) (q : tyOf (u [ τ ]t) ≣ U)
--         → (El u p) [ τ ]T ≡ El (u [ τ ]t) q
--       El[]₂'
--         : (u : Tm Δ) (pu : tyOf u ≣ U)(pu' : tyOf (u [ σ ]t) ≣ U)
--         → tyOf (π₂ {Γ , El (u [ σ ]t) pu'} idS) ≡ El u pu [ σ ∘ π₁ idS ]T
--       Ty-is-set : isSet (Ty Γ)

--     data Sub where
--       ∅S'
--         : Sub Γ ∅
--       _,_∶[_]'
--         : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≣ A [ σ ]T
--         → Sub Γ (Δ , A)
--       idS' : Sub Γ Γ
--       _∘'_
--         : Sub Δ Θ → Sub Γ Δ
--         → Sub Γ Θ
--       π₁'
--         : Sub Γ (Δ , A)
--         → Sub Γ Δ
--       βπ₁'
--         : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≣ A [ σ ]T)
--         → π₁ (σ , t ∶[ p ]) ≡ σ
--       idS∘'_
--         : (σ : Sub Γ Δ)
--         → idS ∘ σ ≡ σ
--       _∘idS'
--         : (σ : Sub Γ Δ)
--         → σ ∘ idS ≡ σ
--       assocS'
--         : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (γ : Sub Θ Ξ)
--         → (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ)
--       ,∘'
--         : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≣ A [ σ ]T)
--           (q : tyOf (t [ τ ]t) ≣ A [ σ ∘ τ ]T)
--         → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ q ])
--       η∅'
--         : (σ : Sub Γ ∅)
--         → σ ≡ ∅S
--       ηπ'
--         : (σ : Sub Γ (Δ , A))
--         → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ])
--     data Tm where
--       _[_] : (A : Tm Δ)(σ : Sub Γ Δ)
--         → Tm Γ
--       π₂'
--         : Sub Γ (Δ , A)
--         → Tm Γ
--       βπ₂'
--         : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≣ A [ σ ]T)
--         → (q : tyOf t ≣ A [ π₁ (σ , t ∶[ p ]) ]T)
--         → π₂ (σ , t ∶[ p ]) ≡ t
--       [idS]t'
--         : (t : Tm Γ)
--         → t ≡ t [ idS ]t
--       [∘]t'
--         : (t : Tm Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
--         → t [ τ ]t [ σ ]t ≡ t [ τ ∘ σ ]t

--     ∅ = ∅'
--     _,_ = _,'_
--     _[_]T = _[_]
--     _[_]t = _[_]
--     U = U'
--     U[] = U[]'
--     El = El'
--     El[] = El[]'
--     El[]₂ = El[]₂'
--     ∅S = ∅S'
--     _,_∶[_] = _,_∶[_]'
--     idS = idS'
--     _∘_ = _∘'_
--     π₁  = π₁'
--     π₂  = π₂'
--     [idS]T = [idS]T'
--     [∘]T = [∘]T'
--     βπ₁ = βπ₁'
--     βπ₂ = βπ₂'
--     idS∘_ = idS∘'_
--     _∘idS = _∘idS'
--     assocS = assocS'
--     ,∘ = ,∘'
--     η∅ = η∅'
--     ηπ = ηπ'
--     [idS]t = [idS]t'
--     [∘]t  = [∘]t'

-- -- --    tyOf (t [ σ ]) = tyOf t [ σ ]T
-- -- --    tyOf (π₂' {Γ} {Δ} {A} σ) = A [ π₁ σ ]T
-- -- --    tyOf (βπ₂' σ t p q i)   = {!p!} -- q i
-- -- --    tyOf ([idS]t' t i)      = [idS]T {A = tyOf t} i
-- -- --    tyOf ([∘]t' t σ τ i)    = [∘]T (tyOf t) σ τ i

-- --     -- equaitons derivable from the computational behaviour of `tyOf
-- --     -- tyOfπ₂ {Γ} {Δ} {A} σ = refl
    tyOfπ₂idS {A = A} {σ = σ} = {!!} -- [∘]T A (π₁ idS) σ
 
-- --   wk : Sub (Γ , A) Γ
-- --   wk = π₁ idS
  
    ⟨,∘⟩
      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≣ A [ σ ]T)
      → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ {!!} ]) -- (σ ∘ τ , t [ τ ]t ∶[ cong _[ τ ] p ∙ [∘]T A τ σ ])
    ⟨,∘⟩ σ t τ p = ,∘ σ t τ p {!!} -- ,∘ σ t τ p {!p!} -- ,∘ σ t τ p _

-- --   ⟨βπ₂⟩
-- --     : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≣ A [ σ ]T)
-- --     → π₂ (σ , t ∶[ p ]) ≡ t 
-- --   ⟨βπ₂⟩ {A = A} σ t p = {!p!} -- βπ₂ σ t _ (cong (A [_]) (βπ₁ σ t p) ∙ sym p)

-- --   π₁∘
-- --     : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
-- --     → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
-- --   π₁∘ {Δ} {Θ} {A} {Γ} τ σ =
-- --     π₁ (τ ∘ σ)
-- --       ≡⟨ cong π₁ (cong (_∘ σ) {!ηπ τ!}) ⟩ -- cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
-- --     π₁ ((π₁ τ , π₂ τ ∶[ ? ]) ∘ σ)
-- --       ≡⟨ cong π₁ {!!} ⟩ -- (⟨,∘⟩ {Δ} {Θ} {Γ} {A} (π₁ {Δ} {Θ} {A} τ) (π₂ {Δ} {Θ} {A} τ) σ (refl {x = A [ π₁ τ ]})) ⟩
-- --     π₁ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ PathToId ([∘]T _ σ (π₁ τ)) ])
-- --       ≡⟨ βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]) {!!} ⟩ -- (cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘]T _ σ (π₁ τ)) ⟩
-- --     π₁ τ ∘ σ
-- --       ∎
      
-- -- --   π₂∘
-- -- --     : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
-- -- --     → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
-- -- --   π₂∘ {Θ = Θ} {A} τ σ = 
-- -- --     π₂ (τ ∘ σ)
-- -- --       ≡⟨ cong π₂ (cong (_∘ σ) (ηπ τ)) ⟩
-- -- --     π₂ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
-- -- --       ≡⟨ cong π₂ (⟨,∘⟩ (π₁ τ) (π₂ τ) σ refl) ⟩
-- -- --     π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ _ ])
-- -- --       ≡⟨ ⟨βπ₂⟩ (π₁ τ ∘ σ) (π₂ τ [ σ ]) _ ⟩
-- -- --     π₂ τ [ σ ]
-- -- --       ∎

-- -- --   π₁idS
-- -- --     : (σ : Sub Γ (Δ , A))
-- -- --     → π₁ σ ≡ π₁ idS ∘ σ
-- -- --   π₁idS σ = 
-- -- --     π₁ σ
-- -- --       ≡⟨ cong π₁ (sym (idS∘ σ)) ⟩
-- -- --     π₁ (idS ∘ σ)
-- -- --       ≡⟨ π₁∘ _ σ ⟩
-- -- --     π₁ idS ∘ σ
-- -- --       ∎

-- -- --   π₂idS
-- -- --     : (σ : Sub Γ (Δ , A))
-- -- --     → π₂ σ ≡ π₂ idS [ σ ]t
-- -- --   π₂idS σ = 
-- -- --     π₂ σ
-- -- --       ≡⟨ cong π₂ (sym (idS∘ σ)) ⟩
-- -- --     π₂ (idS ∘ σ)
-- -- --       ≡⟨ π₂∘ _ _ ⟩
-- -- --     π₂ idS [ σ ]t
-- -- --       ∎

-- -- --   wk∘
-- -- --     : (σ : Sub Γ (Δ , A))
-- -- --     → π₁ σ ≡ wk ∘ σ
-- -- --   wk∘ σ = 
-- -- --     π₁ σ
-- -- --       ≡⟨ cong π₁ (sym (idS∘ σ)) ⟩
-- -- --     π₁ (idS ∘ σ)
-- -- --       ≡⟨ π₁∘ idS σ ⟩
-- -- --     wk ∘ σ
-- -- --       ∎

-- -- --   -- Proofs regarding Boolean
-- -- --   -- Sanity check
-- -- -- {-
-- -- --   ⟨⟩∘=↑∘[]
-- -- --     : (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T) (pb' : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
-- -- --     → ⟨ b ∶[ pb ]⟩𝔹 ∘ σ ≡ (σ ↑𝔹) ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹
-- -- --   ⟨⟩∘=↑∘[] {Δ} {Γ} {σ} b pb pb' =
-- -- --     ⟨ b ∶[ pb ]⟩𝔹 ∘ σ 
-- -- --       ≡⟨ ,∘ idS b σ pb _ ⟩
-- -- --     idS ∘ σ , b [ σ ]t ∶[ _ ]
-- -- --       ≡[ i ]⟨ (idS∘ σ) i , b [ σ ]t ∶[ pb' ∙ 𝔹[σ]≡𝔹[τ] ] ⟩
-- -- --     σ , b [ σ ]t ∶[ _ ]
-- -- --       ≡[ i ]⟨ (σ ∘idS) (~ i) , b [ σ ]t ∶[ pb' ∙ 𝔹[σ]≡𝔹[τ] ] ⟩
-- -- --     σ ∘ idS , b [ σ ]t ∶[ pb' ∙ 𝔹[σ]≡𝔹[τ] ] 
-- -- --       ≡[ i ]⟨ σ ∘ wk∘⟨⟩ (b [ σ ]) pb' (~ i) , vz[⟨b⟩] (b [ σ ]) pb' (~ i) ∶[ {!!} ] ⟩
-- -- --             -- [TODO]: derivable from K?
-- -- --     σ ∘ (π₁ idS ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹) , π₂ idS [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]t ∶[ _ ]
-- -- --       ≡[ i ]⟨ assocS ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 (π₁ idS) σ (~ i) , π₂ idS [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ] ∶[ {!!} ] ⟩
-- -- --             -- [TODO]: derivable from K?
-- -- --     (σ ∘ π₁ idS) ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 , π₂ idS [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]t ∶[ [∘]T _ _ _ ∙ 𝔹[σ]≡𝔹[τ] ]
-- -- --       ≡⟨ sym (,∘ _ _ _ _ _) ⟩
-- -- --     (σ ↑𝔹) ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹
-- -- --       ∎

-- -- --   [⟨⟩∘]=[↑∘[]]
-- -- --     : (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T) (pb' : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
-- -- --     → A [ ⟨ b ∶[ pb ]⟩𝔹 ]T [ σ ]T
-- -- --     ≡ A [ σ ↑𝔹 ]T [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]T
-- -- --   [⟨⟩∘]=[↑∘[]] {Δ} {Γ} {σ} {A} b pb pb' = 
-- -- --     A [ ⟨ b ∶[ pb ]⟩𝔹 ]T [ σ ]T
-- -- --       ≡⟨ [∘]T _ _ _ ⟩
-- -- --     A [ ⟨ b ∶[ pb ]⟩𝔹 ∘ σ ]T
-- -- --       ≡⟨ cong (A [_]) (⟨⟩∘=↑∘[] b pb pb') ⟩
-- -- --     A [ σ ↑𝔹 ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]T
-- -- --       ≡⟨ sym ([∘]T _ _ _) ⟩
-- -- --     A [ σ ↑𝔹 ]T [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]T
-- -- --       ∎

-- -- -- -}

-- -- -- open Foo public
-- -- --   hiding (_,_; _∘_; idS; π₁; π₂; ,∘; βπ₂; ηπ; _[_]T; _[_]t)
-- -- --   renaming
-- -- --   ( _,'_ to _,_
-- -- --   ; _∘'_ to _∘_
-- -- --   ; π₁' to π₁
-- -- --   ; π₂' to π₂
-- -- --   ; idS' to idS
-- -- --   ; ⟨,∘⟩ to ,∘
-- -- --   ; ⟨βπ₂⟩ to βπ₂
-- -- --   ; ηπ' to ηπ
-- -- --   )


-- -- -- -- syntax abbreviations
-- -- -- vz : Tm (Γ , A)
-- -- -- vz = π₂ idS

-- -- -- vs : Tm Γ → Tm (Γ , B)
-- -- -- vs x = x [ wk ]
-- -- -- -- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

-- -- -- -- -- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
-- -- -- -- -- vz:= {Γ} t = idS , t ∶[ {!!} ]
