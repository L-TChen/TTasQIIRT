open import Prelude
  hiding (⋆)
open import Cubical.Foundations.Function


variable
  A B : Set

infixr 10 _⧺_
-- JList is the free monoid over A
data JList (A : Set) : Set where
  []  : JList A
  _⧺_ : JList A → JList A → JList A
  [_] : A → JList A
  ⧺-assoc
    : (xs ys zs : JList A)
    → (xs ⧺ ys) ⧺ zs ≡ xs ⧺ (ys ⧺ zs)
  ⧺-idʳ
    : (xs : JList A)
    → xs ⧺ [] ≡ xs
  ⧺-idˡ
    : (ys : JList A)
    → [] ⧺ ys ≡ ys
  trunc
    : isSet (JList A)

record Model (A X : Set) (XisSet : isSet X) : Set₁ where
  field
    _*_
      : X → X → X
    e : X
    i : A → X
    *-assoc
      : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-idʳ
      : ∀ x → x * e ≡ x
    *-idˡ
      : ∀ x → e * x ≡ x
    
  infixr 10 _*_

  recJ : JList A → X
  recJ []        = e
  recJ (xs ⧺ ys) = recJ xs * recJ ys
  recJ [ x ]     = i x
  recJ (⧺-assoc xs ys zs i) = *-assoc (recJ xs) (recJ ys) (recJ zs) i
  recJ (⧺-idʳ xs i) = *-idʳ (recJ xs) i
  recJ (⧺-idˡ xs i) = *-idˡ (recJ xs) i
  recJ (trunc xs ys p q i j) =
    isSet→SquareP (λ _ _ → XisSet) (cong recJ p) (cong recJ q) refl refl i j

Term : Model A (JList A) trunc
Term {A = A} = record
  { _*_ = _⧺_
  ; e   = []
  ; i   = [_]
  ; *-assoc = ⧺-assoc
  ; *-idʳ   = ⧺-idʳ
  ; *-idˡ   = ⧺-idˡ
  }

record IxJModel (A : Set)
  (P : JList A → Set) (PisSet : ∀ xs → isSet (P xs))
  : Set₁ where

  field
    _⋆_
      : ∀ {x y} → P x → P y
      → P (x ⧺ y)
    𝐞 : P []
    𝐢 : (a : A) → P ([ a ])
    ⋆-assoc
      : ∀ {x y z} (𝐱 : P x) (𝐲 : P y) (𝐳 : P z)
      → PathP (λ i → P (⧺-assoc x y z i)) ((𝐱 ⋆ 𝐲) ⋆ 𝐳) (𝐱 ⋆ (𝐲 ⋆ 𝐳))
    ⋆-idʳ
      : ∀ {x} (𝐱 : P x)
      → PathP (λ i → P (⧺-idʳ x i)) (𝐱 ⋆ 𝐞) 𝐱
    ⋆-idˡ
      : ∀ {x} (𝐱 : P x)
      → PathP (λ i → P (⧺-idˡ x i)) (𝐞 ⋆ 𝐱) 𝐱
 
  infixr 10 _⋆_

  elimJ : (xs : JList A) → P xs
  elimJ []        = 𝐞
  elimJ (xs ⧺ ys) = elimJ xs ⋆ elimJ ys
  elimJ [ x ]     = 𝐢 x
  elimJ (⧺-assoc xs ys zs i) =
    ⋆-assoc (elimJ xs) (elimJ ys) (elimJ zs) i
  elimJ (⧺-idʳ xs i) = ⋆-idʳ (elimJ xs) i
  elimJ (⧺-idˡ xs i) = ⋆-idˡ (elimJ xs) i
  elimJ (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ xs → PisSet _) (elimJ xs) (elimJ ys)
    (cong elimJ p) (cong elimJ q) (trunc xs ys p q) i j

record DJModel (A {X} : Set)
  {XisSet : isSet X} (M : Model A X XisSet)
  (P : X → Set) (PisSet : ∀ x → isSet (P x))
  : Set₁ where
  open Model M

  field
    _⋆_
      : ∀ {x y} → P x → P y
      → P (x * y)
    𝐞 : P e
    𝐢 : (a : A) → P (i a)
    ⋆-assoc
      : {x y z : X} (𝐱 : P x) (𝐲 : P y) (𝐳 : P z)
      → PathP (λ i → P (*-assoc x y z i)) ((𝐱 ⋆ 𝐲) ⋆ 𝐳) (𝐱 ⋆ (𝐲 ⋆ 𝐳))
    ⋆-idʳ
      : {x : X} (𝐱 : P x)
      → PathP (λ i → P (*-idʳ x i)) (𝐱 ⋆ 𝐞) 𝐱
    ⋆-idˡ
      : {x : X} (𝐱 : P x)
      → PathP (λ i → P (*-idˡ x i)) (𝐞 ⋆ 𝐱) 𝐱
 
  infixr 10 _⋆_

  elimJ : (xs : JList A) → P (recJ xs)
  elimJ []        = 𝐞
  elimJ (xs ⧺ ys) = elimJ xs ⋆ elimJ ys
  elimJ [ x ]     = 𝐢 x
  elimJ (⧺-assoc xs ys zs i) =
    ⋆-assoc (elimJ xs) (elimJ ys) (elimJ zs) i
  elimJ (⧺-idʳ xs i) = ⋆-idʳ (elimJ xs) i
  elimJ (⧺-idˡ xs i) = ⋆-idˡ (elimJ xs) i
  elimJ (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ xs → PisSet _) (elimJ xs) (elimJ ys) (cong elimJ p) (cong elimJ q)
      (trunc xs ys p q) i j
open Model using (recJ)
open DJModel using (elimJ)

elimJ'
  : (P : JList A → Set) (PisSet : ∀ xs → isSet (P xs))
  → DJModel A Term P PisSet → (xs : JList A)
  → P (recJ Term xs)
elimJ' P PisSet M = elimJ M 

module _ {A X : Set} {XisSet : isSet X} (M : Model A X XisSet) where
  open Model M
  
  JProp : (P : X → Set) (PisProp : ∀ x → isProp (P x))
    → (_⋆_ : ∀ {x y} → P x → P y → P (x * y))
    → (𝐞 : P e) (𝐢 : (a : A) → P (i a))
    → DJModel A M P λ x → isProp→isSet (PisProp x)
  JProp P PisProp _⋆_ 𝐞 𝐢 = record
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

recTerm=id
  : (xs : JList A)
  → recJ Term xs ≡ xs
recTerm=id []        = refl
recTerm=id (xs ⧺ ys) = cong₂ _⧺_ (recTerm=id xs) (recTerm=id ys)
recTerm=id [ x ]     = refl
recTerm=id (⧺-assoc xs ys zs i) = toPathP {A = λ i → recJ Term (⧺-assoc xs ys zs i) ≡ ⧺-assoc xs ys zs i}
  {λ j → (recTerm=id xs j ⧺ recTerm=id ys j) ⧺ recTerm=id zs j}
  {λ j → recTerm=id xs j ⧺ (recTerm=id ys j ⧺ recTerm=id zs j)}
  (trunc _ _ _ _) i
recTerm=id (⧺-idʳ xs i) = toPathP {A = λ i → recJ Term (⧺-idʳ xs i) ≡ ⧺-idʳ xs i}
  {λ j → recTerm=id xs j ⧺ []}
  {λ j → recTerm=id xs j}
  (trunc _ _ _ _) i
recTerm=id (⧺-idˡ xs i) = toPathP {A = λ i → recJ Term (⧺-idˡ xs i) ≡ ⧺-idˡ xs i}
  {λ j → [] ⧺ recTerm=id xs j}
  {λ j → recTerm=id xs j}
  (trunc _ _ _ _) i
recTerm=id {A} (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2 (λ xs p q p=q p=q' → isSet→isGroupoid trunc (recJ Term xs) xs p q p=q p=q')
  (recTerm=id xs) (recTerm=id ys)
  (cong recTerm=id p) (cong recTerm=id q) (trunc xs ys p q) i j
    
DList : Set → Set
DList A = Σ[ xs ∈ (JList A → JList A) ] ((ys zs : JList A) → xs ys ⧺ zs ≡ xs (ys ⧺ zs))

DListIsSet : isSet (DList A)
DListIsSet = isSetΣSndProp (isSetΠ (λ _ → trunc)) λ _ → isPropΠ (λ _ → isPropΠ (λ _ → trunc _ _))

_++_ : DList A → DList A → DList A
(xs , p) ++ (ys , q) = (λ zs → xs (ys zs))
  , (λ zs as → p (ys zs) as  ∙ cong xs (q zs as))

▷_ : DList A → JList A
▷_ (xs , _) = xs []

DListM : Model A (DList A) DListIsSet
DListM = record
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

◁_ : JList A → DList A
◁_ {A = A} = recJ DListM

▷◁ : (xs : JList A) → ▷ ◁ (recJ Term xs) ≡ recJ Term xs
▷◁ = elimJ (JProp Term (λ xs → ▷ ◁ xs ≡ xs) (λ xs → trunc (▷ ◁ xs) xs)
  (λ {x} {y} p q →
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
    x ⧺ y ∎)
  refl
  λ a → ⧺-idʳ [ a ])

▷◁' : (xs : JList A) → ▷ ◁ xs ≡ xs
▷◁' xs = 
  ▷ ◁ xs
    ≡⟨ cong (▷_ ∘ ◁_) (sym (recTerm=id xs)) ⟩
  ▷ ◁ recJ Term xs
    ≡⟨ ▷◁ xs ⟩
  recJ Term xs
    ≡⟨ recTerm=id xs ⟩
  xs
    ∎
◁≡→≡ : {xs ys : JList A} → (◁ xs) .fst ≡ (◁ ys) .fst → xs ≡ ys
◁≡→≡ {_} {xs} {ys} p = 
  xs
    ≡⟨ sym (▷◁' xs) ⟩
  ▷ ◁ xs
    ≡[ i ]⟨ p i [] ⟩
  ▷ ◁ ys
    ≡⟨ ▷◁' ys ⟩
  ys
    ∎

example
  : {x : A} (xs ys zs : JList A)
  → [ x ] ⧺ xs ⧺ ([] ⧺ ys ⧺ zs) ≡ [ x ] ⧺ (xs ⧺ ys) ⧺ [] ⧺ zs
example xs ys zs = ◁≡→≡ refl

-- the underlying idea is that we can normalise the expression with
-- respect to functional presentation

-- -- -- -- Church encoding? 
-- -- -- {-
-- -- -- module _ {A B : Set} (BisSet : isSet B) (e : B) (_*_ : B → B → B) (i : A → B)
-- -- --   (assoc : ∀ x y z → (x * y) * z ≡ x * (y * z))
-- -- --   (idʳ : ∀ x → x * e ≡ x)
-- -- --   (idˡ : ∀ x → e * x ≡ x) where

-- -- --   recJ : JList A → B
-- -- --   recJ []        = e
-- -- --   recJ (xs ⧺ ys) = recJ xs * recJ ys
-- -- --   recJ [ x ]     = i x
-- -- --   recJ (⧺-assoc xs ys zs i) = assoc (recJ xs) (recJ ys) (recJ zs) i
-- -- --   recJ (⧺-idʳ xs i) = idʳ (recJ xs) i
-- -- --   recJ (⧺-idˡ xs i) = idˡ (recJ xs) i
-- -- --   recJ (trunc xs ys p q i j) =
-- -- --     isSet→SquareP (λ _ _ → BisSet) (cong recJ p) (cong recJ q) refl refl i j

-- -- --   module _ {P : B → Set} (PisSet : ∀ x → isSet (P x))
-- -- --     (pe : P e) (_*P_ : ∀ {x y} → P x → P y → P (x * y)) (iP : ∀ a → P (i a))
-- -- --     (assocP : {x y z : B}(px : P x)(py : P y)(pz : P z) →
-- -- --       PathP (λ i → P (assoc x y z i)) ((px *P py) *P pz) (px *P (py *P pz)))
-- -- --     (idʳP : {x : B}(px : P x) → PathP (λ i → P (idʳ x i)) (px *P pe) px)
-- -- --     (idˡP : {x : B}(px : P x) → PathP (λ i → P (idˡ x i)) (pe *P px) px)
-- -- --     where

-- -- --     elimJ : (xs : JList A) → P (recJ xs)
-- -- --     elimJ []        = pe
-- -- --     elimJ (xs ⧺ ys) = elimJ xs *P elimJ ys
-- -- --     elimJ [ x ]     = iP x
-- -- --     elimJ (⧺-assoc xs ys zs i) = assocP (elimJ xs) (elimJ ys) (elimJ zs) i
-- -- --     elimJ (⧺-idʳ xs i) = idʳP (elimJ xs) i
-- -- --     elimJ (⧺-idˡ xs i) = idˡP (elimJ xs) i
-- -- --     elimJ (trunc xs ys p q i j) = 
-- -- --       isOfHLevel→isOfHLevelDep 2 (λ x → PisSet (recJ x)) (elimJ xs) (elimJ ys) (cong elimJ p) (cong elimJ q) (trunc xs ys p q) i j

-- -- --   module _ {P : B → Set} (PisProp : ∀ x → isProp (P x))
-- -- --     (pe : P e) (_*P_ : ∀ {x y} → P x → P y → P (x * y)) (iP : ∀ a → P (i a))
-- -- --     where

-- -- --     elimJProp : (xs : JList A) → P (recJ xs)
-- -- --     elimJProp = elimJ (λ x → isProp→isSet (PisProp x))
-- -- --       pe _*P_ iP (λ _ _ _ → toPathP (PisProp _ _ _)) (λ _ → toPathP (PisProp _ _ _)) (λ _ → toPathP (PisProp _ _ _))

-- -- -- initial
-- -- --   : (xs : JList A)
-- -- --   → recJ trunc [] _⧺_ [_] ⧺-assoc ⧺-idʳ ⧺-idˡ xs ≡ xs
-- -- -- initial = elimJProp' (λ xs → trunc _ _) refl (λ p q → cong₂ _⧺_ p q) (λ a → refl)

-- -- -- -}

-- -- -- -- -- -- -- data ∥_∥ (A : Set) : Prop where
-- -- -- -- -- -- --   ∣_∣ : A → ∥ A ∥
-- -- -- -- -- -- -- 
-- -- -- -- -- -- -- rec : {A : Set} {B : Prop} → (A → B) → ∥ A ∥ → B
-- -- -- -- -- -- -- rec f ∣ x ∣ = f x
-- -- -- -- -- -- -- 
-- -- -- -- -- -- -- rec2 : {A B : Set} {C : Prop} → (A → B → C) → ∥ A ∥ → ∥ B ∥ → C
-- -- -- -- -- -- -- rec2 f ∣ x ∣ ∣ y ∣ = f x y

-- -- -- -- -- -- -- record Σp (A : Set) (B : A → Prop) : Set where
-- -- -- -- -- -- --   constructor _,_
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     fst : A
-- -- -- -- -- -- --     snd : B fst
-- -- -- -- -- -- -- open Σp public
-- -- -- -- -- -- -- 
-- -- -- -- -- -- -- infixr 4 _,_
-- -- -- -- -- -- -- 
-- -- -- -- -- -- -- Σp-syntax : (A : Set) (B : A → Prop) → Set
-- -- -- -- -- -- -- Σp-syntax = Σp
-- -- -- -- -- -- -- 
-- -- -- -- -- -- -- syntax Σp-syntax A (λ x → B) = Σp[ x ∈ A ] B

-- -- -- -- -- -- -- data List (A : Set) : Set where
-- -- -- -- -- -- --   []  : List A
-- -- -- -- -- -- --   _∷_ : A → List A → List A

-- -- -- -- -- -- -- _++_ : List A → List A → List A
-- -- -- -- -- -- -- []       ++ ys = ys
-- -- -- -- -- -- -- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- -- -- -- -- -- -- infixr 10 _++_ _++'_

-- -- -- -- -- -- -- ++-identityʳ : (xs : List A) → xs ++ [] ≡ xs
-- -- -- -- -- -- -- ++-identityʳ []       = refl
-- -- -- -- -- -- -- ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- -- -- -- -- -- -- ++-assoc
-- -- -- -- -- -- --   : (xs ys zs : List A)
-- -- -- -- -- -- --   → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
-- -- -- -- -- -- -- ++-assoc []       ys zs = refl
-- -- -- -- -- -- -- ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

-- -- -- -- -- -- -- DList : Set → Set
-- -- -- -- -- -- -- DList A = Σp[ xs ∈ (List A → List A) ]
-- -- -- -- -- -- --   ∥ ((ys zs : List A) → xs ys ++ zs ≡ xs (ys ++ zs)) ∥

-- -- -- -- -- -- -- _++'_ : DList A → DList A → DList A
-- -- -- -- -- -- -- (xs , p) ++' (ys , q) = (λ zs → xs (ys zs))
-- -- -- -- -- -- --   , rec2 (λ p q → ∣ (λ zs as → p (ys zs) as ∙ cong xs (q zs as)) ∣) p q

-- -- -- -- -- -- -- []' : DList A
-- -- -- -- -- -- -- []' = (λ ys → ys) , ∣ (λ _ _ → refl) ∣

-- -- -- -- -- -- -- ++'-identityʳ : (xs : DList A) → xs ++' []' ≡ xs
-- -- -- -- -- -- -- ++'-identityʳ xs = refl

-- -- -- -- -- -- -- ++'-assoc
-- -- -- -- -- -- --   : (xs ys zs : DList A)
-- -- -- -- -- -- --   → (xs ++' ys) ++' zs ≡ xs ++' ys ++' zs
-- -- -- -- -- -- -- ++'-assoc xs ys zs = refl

-- -- -- -- -- -- -- data JList (A : Set) : Set
-- -- -- -- -- -- -- flatten : JList A → List A

-- -- -- -- -- -- -- data JList A where
-- -- -- -- -- -- --   []  : JList A
-- -- -- -- -- -- --   [_] : A → JList A
-- -- -- -- -- -- --   _⧺_ : JList A → JList A → JList A
-- -- -- -- -- -- --   nf : (xs ys : JList A) → flatten xs ≡ flatten ys → xs ≡ ys
  
-- -- -- -- -- -- -- flatten []        = []
-- -- -- -- -- -- -- flatten [ x ]     = x ∷ []
-- -- -- -- -- -- -- flatten (xs ⧺ ys) = flatten xs ++ flatten ys
-- -- -- -- -- -- -- flatten (nf xs ys x i) = x i

-- -- -- -- -- -- -- fromList : List A → DList A
-- -- -- -- -- -- -- fromList xs = (λ ys → xs ++ ys) , ∣ ++-assoc xs ∣

-- -- -- -- -- -- -- toList : DList A → List A
-- -- -- -- -- -- -- toList (xs , _) = xs []

-- -- -- -- -- -- -- fromJList : JList A → DList A
-- -- -- -- -- -- -- fromJList []        = (λ xs → xs) , ∣ (λ _ _ → refl) ∣
-- -- -- -- -- -- -- fromJList [ x ]     = (λ xs → x ∷ xs) , ∣ (λ _ _ → refl) ∣
-- -- -- -- -- -- -- fromJList (xs ⧺ ys) = fromJList xs ++' fromJList ys
-- -- -- -- -- -- -- fromJList (nf xs xs' p i) = {!!} -- (λ zs → {!!}) , ∣ {!λ !} ∣

-- -- -- -- -- -- -- postulate
-- -- -- -- -- -- --   toJList : DList A → JList A
-- -- -- -- -- -- --   toJList-fromJList
-- -- -- -- -- -- --     : (xs : JList A) → toJList (fromJList xs) ≡ xs
-- -- -- -- -- -- -- -- toJList (xs , p) = {!!}
-- -- -- -- -- -- -- postulate
-- -- -- -- -- -- --   fromList-toList : (xs : DList A) → fromList (toList xs) ≡ xs -- List needs to be a set
-- -- -- -- -- -- -- --  (xs []) ++_ , _
-- -- -- -- -- -- -- --    ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- --  (λ ys → xs ([] ++ ys)) , p
-- -- -- -- -- -- -- --    ≡⟨ refl ⟩
-- -- -- -- -- -- -- --  xs , p
-- -- -- -- -- -- -- --    ∎ 

-- -- -- -- -- -- -- toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
-- -- -- -- -- -- -- toList-fromList = ++-identityʳ

-- -- -- -- -- -- -- fromList++
-- -- -- -- -- -- --   : (xs ys : List A)
-- -- -- -- -- -- --   → fromList (xs ++ ys) ≡ fromList xs ++' fromList ys
-- -- -- -- -- -- -- fromList++ xs ys i = (λ zs → ++-assoc xs ys zs i) , ∣ (λ ys zs → {!!}) ∣ -- requires that List is a set 

-- -- -- -- -- -- -- example
-- -- -- -- -- -- --   : (xs ys zs : List A)
-- -- -- -- -- -- --   → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
-- -- -- -- -- -- -- example xs ys zs =
-- -- -- -- -- -- --   xs ++ ys ++ zs
-- -- -- -- -- -- --     ≡⟨ sym $ toList-fromList _ ⟩
-- -- -- -- -- -- --   toList (fromList (xs ++ ys ++ zs))
-- -- -- -- -- -- --     ≡⟨ cong toList (fromList++ xs (ys ++ zs)) ⟩
-- -- -- -- -- -- --   toList (fromList xs ++' (fromList (ys ++ zs)))
-- -- -- -- -- -- --     ≡⟨ cong toList (cong (fromList xs ++'_) (fromList++ ys zs)) ⟩
-- -- -- -- -- -- --   toList (fromList xs ++' (fromList ys ++' fromList zs))
-- -- -- -- -- -- --     ≡⟨ refl ⟩
-- -- -- -- -- -- --   toList ((fromList xs ++' fromList ys) ++' fromList zs)
-- -- -- -- -- -- --     ≡⟨ cong toList (cong (_++' fromList zs) (sym $ fromList++ xs ys)) ⟩
-- -- -- -- -- -- --   toList (fromList (xs ++ ys) ++' fromList zs)
-- -- -- -- -- -- --     ≡⟨ cong toList (sym $ fromList++ (xs ++ ys) zs) ⟩
-- -- -- -- -- -- --   toList (fromList ((xs ++ ys) ++ zs))
-- -- -- -- -- -- --     ≡⟨ toList-fromList _ ⟩
-- -- -- -- -- -- --   (xs ++ ys) ++ zs
-- -- -- -- -- -- --     ∎

-- -- -- -- -- -- -- example2
-- -- -- -- -- -- --   : (xs ys zs : JList A)
-- -- -- -- -- -- --   → xs ⧺ (ys ⧺ zs) ≡ (xs ⧺ ys) ⧺ zs
-- -- -- -- -- -- -- example2 xs ys zs =
-- -- -- -- -- -- --     sym (toJList-fromJList (xs ⧺ (ys ⧺ zs)))
-- -- -- -- -- -- -- --  ∙ cong toJList lemma
-- -- -- -- -- -- --   ∙ toJList-fromJList ((xs ⧺ ys) ⧺ zs) 
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --     lemma : fromJList (xs ⧺ (ys ⧺ zs)) ≡ fromJList ((xs ⧺ ys) ⧺ zs)
-- -- -- -- -- -- --     lemma = refl
