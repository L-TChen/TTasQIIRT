open import Prelude
  hiding (⋆; rec)
  
open import Cubical.Foundations.Function

module Difference (A : Set) where

infixr 10 _⧺_

record IsModel (X : Set) (XisSet : isSet X) : Set₁ where
  infixr 10 _*_
  
  field
    _*_
      : X → X → X
    e : X
    i : A → X
    *-assoc
      : ∀ x y z → (x * y) * z ≡ x * y * z
    *-idʳ
      : ∀ x → x * e ≡ x
    *-idˡ
      : ∀ x → e * x ≡ x

record Model : Set₁ where
  field
    X : Set
    XisSet : isSet X
    isModel : IsModel X XisSet

  open IsModel isModel public
    
record IsDepModel {X : Set} {XisSet : isSet X} (M : IsModel X XisSet)
  (P : X → Set) (PisSet : ∀ x → isSet (P x)) : Set₁ where
  open IsModel M
  
  infixr 10 _⋆_

  field
    _⋆_
      : ∀ {x y} → P x → P y
      → P (x * y)
    𝐞 : P e
    𝐢 : (a : A) → P (i a)

  infix 4 PathP-fam
  PathP-fam : {x y : X} → P x → x ≡ y → P y → Type
  PathP-fam px e py = PathP (λ i → P (e i)) px py

  syntax PathP-fam px e py = px ≡[ e ] py
  field
    ⋆-assoc
      : ∀ {x y z} (𝐱 : P x) (𝐲 : P y) (𝐳 : P z)
      → (𝐱 ⋆ 𝐲) ⋆ 𝐳 ≡[ *-assoc x y z ] 𝐱 ⋆ 𝐲 ⋆ 𝐳
    ⋆-idʳ
      : ∀ {x} (𝐱 : P x)
      → 𝐱 ⋆ 𝐞 ≡[ *-idʳ x ] 𝐱
    ⋆-idˡ
      : ∀ {x} (𝐱 : P x)
      → 𝐞 ⋆ 𝐱 ≡[ *-idˡ x ] 𝐱


record DepModel (M : Model) : Type₁ where
  open Model M

  field
    P      : X → Type
    PisSet : ∀ x → isSet (P x)
    DM : IsDepModel isModel P PisSet

  open IsDepModel DM public

record IsModelProp {X : Type} {XisSet : isSet X} (M : IsModel X XisSet)
  (P : X → Type) (PisSet : ∀ x → isProp (P x)) : Set₁ where
  open IsModel M

  field
    _⋆_
      : ∀ {x y} → P x → P y
      → P (x * y)
    𝐞 : P e
    𝐢 : (a : A) → P (i a)

record ModelProp (M : Model) : Set₁ where
  open Model M

  field
    P : X → Type
    PisProp : ∀ x → isProp (P x)
    MP : IsModelProp isModel P PisProp

  open IsModelProp MP public
  
ModelProp→DepModel
  : {M : Model} → ModelProp M → DepModel M
ModelProp→DepModel {M} mp =
  let open ModelProp mp
      open Model M in record
  { P = P
  ; PisSet = λ x → isProp→isSet (PisProp x)
  ; DM = record -- MP it would be nice to have a syntax for record extension
    { _⋆_ = _⋆_
    ; 𝐞   = 𝐞
    ; 𝐢   = 𝐢
    ; ⋆-assoc = λ {x} {y} {z} 𝐱 𝐲 𝐳 →
      toPathP {_} {λ i → P (*-assoc x y z i)} {(𝐱 ⋆ 𝐲) ⋆ 𝐳} {𝐱 ⋆ (𝐲 ⋆ 𝐳)}
        (PisProp (x * (y * z))
          (transport (λ i → P (*-assoc x y z i)) ((𝐱 ⋆ 𝐲) ⋆ 𝐳))
          (𝐱 ⋆ (𝐲 ⋆ 𝐳)))
    ; ⋆-idʳ   = λ _ → toPathP (PisProp _ _ _)
    ; ⋆-idˡ   = λ _ → toPathP (PisProp _ _ _)
    }
  }

data JList : Set where
  []  : JList
  _⧺_ : JList → JList → JList
  [_] : A → JList
  ⧺-assoc
    : (xs ys zs : JList)
    → (xs ⧺ ys) ⧺ zs ≡ xs ⧺ (ys ⧺ zs)
  ⧺-idʳ
    : (xs : JList)
    → xs ⧺ [] ≡ xs
  ⧺-idˡ
    : (ys : JList)
    → [] ⧺ ys ≡ ys
  trunc
    : isSet (JList)

Term : Model
Term = record
  { X       = JList
  ; XisSet  = trunc
  ; isModel = record
    { _*_ = _⧺_
    ; e   = []
    ; i   = [_]
    ; *-assoc = ⧺-assoc
    ; *-idʳ   = ⧺-idʳ
    ; *-idˡ   = ⧺-idˡ
    }
  }

module Elimitor (C : DepModel Term) where
  open Model    Term
  open DepModel C

  elim : (xs : JList) → P xs
  elim []        = 𝐞
  elim (xs ⧺ ys) = elim xs ⋆ elim ys
  elim [ x ]     = 𝐢 x
  elim (⧺-assoc xs ys zs i) =
    ⋆-assoc (elim xs) (elim ys) (elim zs) i
  elim (⧺-idʳ xs i) = ⋆-idʳ (elim xs) i
  elim (⧺-idˡ xs i) = ⋆-idˡ (elim xs) i
  elim (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ xs → PisSet _) (elim xs) (elim ys)
    (cong elim p) (cong elim q) (trunc xs ys p q) i j

open Elimitor

module Recursor (M : Model) where
  open Model    M

  rec : JList → X
  rec []        = e
  rec (xs ⧺ ys) = rec xs * rec ys
  rec [ x ]     = i x
  rec (⧺-assoc xs ys zs i) = *-assoc (rec xs) (rec ys) (rec zs) i
  rec (⧺-idʳ xs i) = *-idʳ (rec xs) i
  rec (⧺-idˡ xs i) = *-idˡ (rec xs) i
  rec (trunc xs ys p q i j) =
    XisSet (rec xs) (rec ys) (cong rec p) (cong rec q) i j
open Recursor
    
DList : Set
DList = Σ[ xs ∈ (JList → JList) ] ((ys zs : JList) → xs ys ⧺ zs ≡ xs (ys ⧺ zs))

DListIsSet : isSet DList
DListIsSet = isSetΣSndProp (isSetΠ (λ _ → trunc)) λ _ → isPropΠ (λ _ → isPropΠ (λ _ → trunc _ _))

_++_ : DList → DList → DList
(xs , p) ++ (ys , q) = (λ zs → xs (ys zs))
  , (λ zs as → p (ys zs) as  ∙ cong xs (q zs as))

▷_ : DList → JList
▷_ (xs , _) = xs []

DListMod : Model
DListMod = record { X = DList ; XisSet = DListIsSet ; isModel = DListIsModel }
  where
    DListIsModel = record
      { _*_ = _++_
      ; e   = (λ xs → xs) , λ _ _ → refl
      ; i   = λ x → [ x ] ⧺_ , ⧺-assoc [ x ]
      ; *-assoc = λ xs ys zs
        → ΣPathP (refl , funExt (λ xs → funExt (λ ys → trunc _ _ _ _)))
      ; *-idʳ   = λ xs
        → ΣPathP (refl , funExt (λ xs → funExt (λ ys → trunc _ _ _ _)))
      ; *-idˡ   = λ xs
        → ΣPathP (refl , funExt (λ xs → funExt (λ ys → trunc _ _ _ _)))
      }

◁_ : JList → DList
◁_ = rec DListMod 

▷◁ : (xs : JList) → ▷ ◁ xs ≡ xs
▷◁ = elim $ ModelProp→DepModel
  record
    { P  = λ xs → ▷ ◁ xs ≡ xs ; PisProp = λ xs → trunc (▷ ◁ xs) xs
    ; MP = record
      { _⋆_ = λ {x} {y} p q →
          ▷ (◁ (x ⧺ y))
            ≡⟨⟩
          (◁ x) .fst ((◁ y) .fst [])
            ≡⟨ cong ((◁ x) .fst) q ⟩
          (◁ x) .fst y
            ≡⟨ cong ((◁ x) .fst) (sym $ ⧺-idˡ y) ⟩
          (◁ x) .fst ([] ⧺ y)
            ≡⟨ sym ((◁ x) .snd [] y) ⟩
          ((◁ x) .fst []) ⧺ y
            ≡⟨ cong (_⧺ y) p ⟩
          x ⧺ y ∎
      ; 𝐞 = refl
      ; 𝐢 = ⧺-idʳ ∘ [_] }
      }

◁≡→≡ : {xs ys : JList} → (◁ xs) .fst ≡ (◁ ys) .fst → xs ≡ ys
◁≡→≡ {xs} {ys} p = 
  xs
    ≡⟨ sym (▷◁ xs) ⟩
  ▷ ◁ xs
    ≡[ i ]⟨ p i [] ⟩
  ▷ ◁ ys
    ≡⟨ ▷◁ ys ⟩
  ys
    ∎

example
  : {x : A} (xs ys zs : JList)
  → [ x ] ⧺ xs ⧺ ([] ⧺ ys ⧺ zs) ≡ [ x ] ⧺ (xs ⧺ ys) ⧺ [] ⧺ zs
example xs ys zs = ◁≡→≡ refl

open import Cubical.Data.Nat
  hiding (elim)
len : DList → ℕ
len xs = rec
  (record { X = ℕ ; XisSet = isSetℕ ; isModel = record
     { _*_ = _+_
     ; e   = 0
     ; i   = λ _ → 1
     ; *-assoc = λ x y z → sym (+-assoc x y z) ; *-idʳ = +-zero ; *-idˡ = λ x → refl
     }
     })
  (▷ xs)

revᵣ : Model
revᵣ = record { X = DList ; XisSet = DListIsSet ; isModel = let open Model DListMod in record
  { _*_ = λ xs ys → ys ++ xs
  ; e   = e
  ; i   = i
  ; *-assoc = λ x y z → sym (*-assoc z y x)
  ; *-idʳ = *-idˡ
  ; *-idˡ = *-idʳ }
  }

reverse : DList → DList
reverse xs = rec revᵣ (▷ xs)

reverse² : (xs : DList) → reverse (reverse xs) ≡ xs
reverse² xs = elim (record { P = λ xs → {!rec revᵣ xs!} ; PisSet = {!!} ; DM = {!!} }) (▷ xs)

-- -- -- -- -- -- -- -- Church encoding? 
-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- module _ {A B : Set} (BisSet : isSet B) (e : B) (_*_ : B → B → B) (i : A → B)
-- -- -- -- -- -- --   (assoc : ∀ x y z → (x * y) * z ≡ x * (y * z))
-- -- -- -- -- -- --   (idʳ : ∀ x → x * e ≡ x)
-- -- -- -- -- -- --   (idˡ : ∀ x → e * x ≡ x) where

-- -- -- -- -- -- --   recJ : JList A → B
-- -- -- -- -- -- --   recJ []        = e
-- -- -- -- -- -- --   recJ (xs ⧺ ys) = recJ xs * recJ ys
-- -- -- -- -- -- --   recJ [ x ]     = i x
-- -- -- -- -- -- --   recJ (⧺-assoc xs ys zs i) = assoc (recJ xs) (recJ ys) (recJ zs) i
-- -- -- -- -- -- --   recJ (⧺-idʳ xs i) = idʳ (recJ xs) i
-- -- -- -- -- -- --   recJ (⧺-idˡ xs i) = idˡ (recJ xs) i
-- -- -- -- -- -- --   recJ (trunc xs ys p q i j) =
-- -- -- -- -- -- --     isSet→SquareP (λ _ _ → BisSet) (cong recJ p) (cong recJ q) refl refl i j

-- -- -- -- -- -- --   module _ {P : B → Set} (PisSet : ∀ x → isSet (P x))
-- -- -- -- -- -- --     (pe : P e) (_*P_ : ∀ {x y} → P x → P y → P (x * y)) (iP : ∀ a → P (i a))
-- -- -- -- -- -- --     (assocP : {x y z : B}(px : P x)(py : P y)(pz : P z) →
-- -- -- -- -- -- --       PathP (λ i → P (assoc x y z i)) ((px *P py) *P pz) (px *P (py *P pz)))
-- -- -- -- -- -- --     (idʳP : {x : B}(px : P x) → PathP (λ i → P (idʳ x i)) (px *P pe) px)
-- -- -- -- -- -- --     (idˡP : {x : B}(px : P x) → PathP (λ i → P (idˡ x i)) (pe *P px) px)
-- -- -- -- -- -- --     where

-- -- -- -- -- -- --     elimJ : (xs : JList A) → P (recJ xs)
-- -- -- -- -- -- --     elimJ []        = pe
-- -- -- -- -- -- --     elimJ (xs ⧺ ys) = elimJ xs *P elimJ ys
-- -- -- -- -- -- --     elimJ [ x ]     = iP x
-- -- -- -- -- -- --     elimJ (⧺-assoc xs ys zs i) = assocP (elimJ xs) (elimJ ys) (elimJ zs) i
-- -- -- -- -- -- --     elimJ (⧺-idʳ xs i) = idʳP (elimJ xs) i
-- -- -- -- -- -- --     elimJ (⧺-idˡ xs i) = idˡP (elimJ xs) i
-- -- -- -- -- -- --     elimJ (trunc xs ys p q i j) = 
-- -- -- -- -- -- --       isOfHLevel→isOfHLevelDep 2 (λ x → PisSet (recJ x)) (elimJ xs) (elimJ ys) (cong elimJ p) (cong elimJ q) (trunc xs ys p q) i j

-- -- -- -- -- -- --   module _ {P : B → Set} (PisProp : ∀ x → isProp (P x))
-- -- -- -- -- -- --     (pe : P e) (_*P_ : ∀ {x y} → P x → P y → P (x * y)) (iP : ∀ a → P (i a))
-- -- -- -- -- -- --     where

-- -- -- -- -- -- --     elimJProp : (xs : JList A) → P (recJ xs)
-- -- -- -- -- -- --     elimJProp = elimJ (λ x → isProp→isSet (PisProp x))
-- -- -- -- -- -- --       pe _*P_ iP (λ _ _ _ → toPathP (PisProp _ _ _)) (λ _ → toPathP (PisProp _ _ _)) (λ _ → toPathP (PisProp _ _ _))

-- -- -- -- -- -- -- initial
-- -- -- -- -- -- --   : (xs : JList A)
-- -- -- -- -- -- --   → recJ trunc [] _⧺_ [_] ⧺-assoc ⧺-idʳ ⧺-idˡ xs ≡ xs
-- -- -- -- -- -- -- initial = elimJProp' (λ xs → trunc _ _) refl (λ p q → cong₂ _⧺_ p q) (λ a → refl)

-- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- data ∥_∥ (A : Set) : Prop where
-- -- -- -- -- -- -- -- -- -- --   ∣_∣ : A → ∥ A ∥
-- -- -- -- -- -- -- -- -- -- -- 
-- -- -- -- -- -- -- -- -- -- -- rec : {A : Set} {B : Prop} → (A → B) → ∥ A ∥ → B
-- -- -- -- -- -- -- -- -- -- -- rec f ∣ x ∣ = f x
-- -- -- -- -- -- -- -- -- -- -- 
-- -- -- -- -- -- -- -- -- -- -- rec2 : {A B : Set} {C : Prop} → (A → B → C) → ∥ A ∥ → ∥ B ∥ → C
-- -- -- -- -- -- -- -- -- -- -- rec2 f ∣ x ∣ ∣ y ∣ = f x y

-- -- -- -- -- -- -- -- -- -- -- record Σp (A : Set) (B : A → Prop) : Set where
-- -- -- -- -- -- -- -- -- -- --   constructor _,_
-- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- --     fst : A
-- -- -- -- -- -- -- -- -- -- --     snd : B fst
-- -- -- -- -- -- -- -- -- -- -- open Σp public
-- -- -- -- -- -- -- -- -- -- -- 
-- -- -- -- -- -- -- -- -- -- -- infixr 4 _,_
-- -- -- -- -- -- -- -- -- -- -- 
-- -- -- -- -- -- -- -- -- -- -- Σp-syntax : (A : Set) (B : A → Prop) → Set
-- -- -- -- -- -- -- -- -- -- -- Σp-syntax = Σp
-- -- -- -- -- -- -- -- -- -- -- 
-- -- -- -- -- -- -- -- -- -- -- syntax Σp-syntax A (λ x → B) = Σp[ x ∈ A ] B

-- -- -- -- -- -- -- -- -- -- -- data List (A : Set) : Set where
-- -- -- -- -- -- -- -- -- -- --   []  : List A
-- -- -- -- -- -- -- -- -- -- --   _∷_ : A → List A → List A

-- -- -- -- -- -- -- -- -- -- -- _++_ : List A → List A → List A
-- -- -- -- -- -- -- -- -- -- -- []       ++ ys = ys
-- -- -- -- -- -- -- -- -- -- -- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- -- -- -- -- -- -- -- -- -- -- infixr 10 _++_ _++'_

-- -- -- -- -- -- -- -- -- -- -- ++-identityʳ : (xs : List A) → xs ++ [] ≡ xs
-- -- -- -- -- -- -- -- -- -- -- ++-identityʳ []       = refl
-- -- -- -- -- -- -- -- -- -- -- ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- -- -- -- -- -- -- -- -- -- -- ++-assoc
-- -- -- -- -- -- -- -- -- -- --   : (xs ys zs : List A)
-- -- -- -- -- -- -- -- -- -- --   → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
-- -- -- -- -- -- -- -- -- -- -- ++-assoc []       ys zs = refl
-- -- -- -- -- -- -- -- -- -- -- ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

-- -- -- -- -- -- -- -- -- -- -- DList : Set → Set
-- -- -- -- -- -- -- -- -- -- -- DList A = Σp[ xs ∈ (List A → List A) ]
-- -- -- -- -- -- -- -- -- -- --   ∥ ((ys zs : List A) → xs ys ++ zs ≡ xs (ys ++ zs)) ∥

-- -- -- -- -- -- -- -- -- -- -- _++'_ : DList A → DList A → DList A
-- -- -- -- -- -- -- -- -- -- -- (xs , p) ++' (ys , q) = (λ zs → xs (ys zs))
-- -- -- -- -- -- -- -- -- -- --   , rec2 (λ p q → ∣ (λ zs as → p (ys zs) as ∙ cong xs (q zs as)) ∣) p q

-- -- -- -- -- -- -- -- -- -- -- []' : DList A
-- -- -- -- -- -- -- -- -- -- -- []' = (λ ys → ys) , ∣ (λ _ _ → refl) ∣

-- -- -- -- -- -- -- -- -- -- -- ++'-identityʳ : (xs : DList A) → xs ++' []' ≡ xs
-- -- -- -- -- -- -- -- -- -- -- ++'-identityʳ xs = refl

-- -- -- -- -- -- -- -- -- -- -- ++'-assoc
-- -- -- -- -- -- -- -- -- -- --   : (xs ys zs : DList A)
-- -- -- -- -- -- -- -- -- -- --   → (xs ++' ys) ++' zs ≡ xs ++' ys ++' zs
-- -- -- -- -- -- -- -- -- -- -- ++'-assoc xs ys zs = refl

-- -- -- -- -- -- -- -- -- -- -- data JList (A : Set) : Set
-- -- -- -- -- -- -- -- -- -- -- flatten : JList A → List A

-- -- -- -- -- -- -- -- -- -- -- data JList A where
-- -- -- -- -- -- -- -- -- -- --   []  : JList A
-- -- -- -- -- -- -- -- -- -- --   [_] : A → JList A
-- -- -- -- -- -- -- -- -- -- --   _⧺_ : JList A → JList A → JList A
-- -- -- -- -- -- -- -- -- -- --   nf : (xs ys : JList A) → flatten xs ≡ flatten ys → xs ≡ ys
  
-- -- -- -- -- -- -- -- -- -- -- flatten []        = []
-- -- -- -- -- -- -- -- -- -- -- flatten [ x ]     = x ∷ []
-- -- -- -- -- -- -- -- -- -- -- flatten (xs ⧺ ys) = flatten xs ++ flatten ys
-- -- -- -- -- -- -- -- -- -- -- flatten (nf xs ys x i) = x i

-- -- -- -- -- -- -- -- -- -- -- fromList : List A → DList A
-- -- -- -- -- -- -- -- -- -- -- fromList xs = (λ ys → xs ++ ys) , ∣ ++-assoc xs ∣

-- -- -- -- -- -- -- -- -- -- -- toList : DList A → List A
-- -- -- -- -- -- -- -- -- -- -- toList (xs , _) = xs []

-- -- -- -- -- -- -- -- -- -- -- fromJList : JList A → DList A
-- -- -- -- -- -- -- -- -- -- -- fromJList []        = (λ xs → xs) , ∣ (λ _ _ → refl) ∣
-- -- -- -- -- -- -- -- -- -- -- fromJList [ x ]     = (λ xs → x ∷ xs) , ∣ (λ _ _ → refl) ∣
-- -- -- -- -- -- -- -- -- -- -- fromJList (xs ⧺ ys) = fromJList xs ++' fromJList ys
-- -- -- -- -- -- -- -- -- -- -- fromJList (nf xs xs' p i) = {!!} -- (λ zs → {!!}) , ∣ {!λ !} ∣

-- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- --   toJList : DList A → JList A
-- -- -- -- -- -- -- -- -- -- --   toJList-fromJList
-- -- -- -- -- -- -- -- -- -- --     : (xs : JList A) → toJList (fromJList xs) ≡ xs
-- -- -- -- -- -- -- -- -- -- -- -- toJList (xs , p) = {!!}
-- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- --   fromList-toList : (xs : DList A) → fromList (toList xs) ≡ xs -- List needs to be a set
-- -- -- -- -- -- -- -- -- -- -- --  (xs []) ++_ , _
-- -- -- -- -- -- -- -- -- -- -- --    ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --  (λ ys → xs ([] ++ ys)) , p
-- -- -- -- -- -- -- -- -- -- -- --    ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- --  xs , p
-- -- -- -- -- -- -- -- -- -- -- --    ∎ 

-- -- -- -- -- -- -- -- -- -- -- toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
-- -- -- -- -- -- -- -- -- -- -- toList-fromList = ++-identityʳ

-- -- -- -- -- -- -- -- -- -- -- fromList++
-- -- -- -- -- -- -- -- -- -- --   : (xs ys : List A)
-- -- -- -- -- -- -- -- -- -- --   → fromList (xs ++ ys) ≡ fromList xs ++' fromList ys
-- -- -- -- -- -- -- -- -- -- -- fromList++ xs ys i = (λ zs → ++-assoc xs ys zs i) , ∣ (λ ys zs → {!!}) ∣ -- requires that List is a set 

-- -- -- -- -- -- -- -- -- -- -- example
-- -- -- -- -- -- -- -- -- -- --   : (xs ys zs : List A)
-- -- -- -- -- -- -- -- -- -- --   → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
-- -- -- -- -- -- -- -- -- -- -- example xs ys zs =
-- -- -- -- -- -- -- -- -- -- --   xs ++ ys ++ zs
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ sym $ toList-fromList _ ⟩
-- -- -- -- -- -- -- -- -- -- --   toList (fromList (xs ++ ys ++ zs))
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ cong toList (fromList++ xs (ys ++ zs)) ⟩
-- -- -- -- -- -- -- -- -- -- --   toList (fromList xs ++' (fromList (ys ++ zs)))
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ cong toList (cong (fromList xs ++'_) (fromList++ ys zs)) ⟩
-- -- -- -- -- -- -- -- -- -- --   toList (fromList xs ++' (fromList ys ++' fromList zs))
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- --   toList ((fromList xs ++' fromList ys) ++' fromList zs)
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ cong toList (cong (_++' fromList zs) (sym $ fromList++ xs ys)) ⟩
-- -- -- -- -- -- -- -- -- -- --   toList (fromList (xs ++ ys) ++' fromList zs)
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ cong toList (sym $ fromList++ (xs ++ ys) zs) ⟩
-- -- -- -- -- -- -- -- -- -- --   toList (fromList ((xs ++ ys) ++ zs))
-- -- -- -- -- -- -- -- -- -- --     ≡⟨ toList-fromList _ ⟩
-- -- -- -- -- -- -- -- -- -- --   (xs ++ ys) ++ zs
-- -- -- -- -- -- -- -- -- -- --     ∎

-- -- -- -- -- -- -- -- -- -- -- example2
-- -- -- -- -- -- -- -- -- -- --   : (xs ys zs : JList A)
-- -- -- -- -- -- -- -- -- -- --   → xs ⧺ (ys ⧺ zs) ≡ (xs ⧺ ys) ⧺ zs
-- -- -- -- -- -- -- -- -- -- -- example2 xs ys zs =
-- -- -- -- -- -- -- -- -- -- --     sym (toJList-fromJList (xs ⧺ (ys ⧺ zs)))
-- -- -- -- -- -- -- -- -- -- -- --  ∙ cong toJList lemma
-- -- -- -- -- -- -- -- -- -- --   ∙ toJList-fromJList ((xs ⧺ ys) ⧺ zs) 
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --     lemma : fromJList (xs ⧺ (ys ⧺ zs)) ≡ fromJList ((xs ⧺ ys) ⧺ zs)
-- -- -- -- -- -- -- -- -- -- --     lemma = refl
