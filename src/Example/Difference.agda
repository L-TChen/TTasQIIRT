open import Prelude
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
  
module _ {A B : Set} (BisSet : isSet B) (e : B) (_*_ : B → B → B) (i : A → B)
  (assoc : ∀ x y z → (x * y) * z ≡ x * (y * z))
  (idʳ : ∀ x → x * e ≡ x)
  (idˡ : ∀ x → e * x ≡ x) where

  recJ : JList A → B
  recJ []        = e
  recJ (xs ⧺ ys) = recJ xs * recJ ys
  recJ [ x ]     = i x
  recJ (⧺-assoc xs ys zs i) = assoc (recJ xs) (recJ ys) (recJ zs) i
  recJ (⧺-idʳ xs i) = idʳ (recJ xs) i
  recJ (⧺-idˡ xs i) = idˡ (recJ xs) i
  recJ (trunc xs ys p q i j) =
    isSet→SquareP (λ _ _ → BisSet) (cong recJ p) (cong recJ q) refl refl i j

module _ {P : JList A → Set} (PisSet : ∀ x → isSet (P x))
  (e : P []) (_*_ : ∀ {x y} → P x → P y → P (x ⧺ y)) (i : ∀ a → P [ a ])
  (assocP : {x y z : JList A}(px : P x)(py : P y)(pz : P z) →
    PathP (λ i → P (⧺-assoc x y z i)) ((px * py) * pz) (px * (py * pz)))
  (idʳP : {xs : JList A}(x : P xs) → PathP (λ i → P (⧺-idʳ xs i)) (x  * e) x)
  (idˡP : {xs : JList A}(x : P xs) → PathP (λ i → P (⧺-idˡ xs i)) (e * x)  x)
  where

  elimJ : (xs : JList A) → P xs
  elimJ []        = e
  elimJ (xs ⧺ ys) = elimJ xs * elimJ ys
  elimJ [ x ]     = i x
  elimJ (⧺-assoc xs ys zs i) = assocP (elimJ xs) (elimJ ys) (elimJ zs) i
  elimJ (⧺-idʳ xs i) = idʳP (elimJ xs) i
  elimJ (⧺-idˡ xs i) = idˡP (elimJ xs) i
  elimJ (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 PisSet (elimJ xs) (elimJ ys) (cong elimJ p) (cong elimJ q) (trunc xs ys p q) i j

module _ {P : JList A → Set} (PisProp : ∀ x → isProp (P x))
  (e : P []) (_*_ : ∀ {x y} → P x → P y → P (x ⧺ y)) (i : ∀ a → P [ a ])
  where
  elimJProp : (xs : JList A) → P xs
  elimJProp = elimJ ((λ x → isProp→isSet (PisProp x))) e _*_ i
    (λ _ _ _ → toPathP (PisProp _ _ _))
    (λ _ → toPathP (PisProp _ _ _))
    (λ _ → toPathP (PisProp _ _ _))
    
DList : Set → Set
DList A = Σ[ xs ∈ (JList A → JList A) ] ((ys zs : JList A) → xs ys ⧺ zs ≡ xs (ys ⧺ zs))

DListIsSet : isSet (DList A)
DListIsSet = isSetΣSndProp (isSetΠ (λ _ → trunc)) λ _ → isPropΠ (λ _ → isPropΠ (λ _ → trunc _ _))

_++_ : DList A → DList A → DList A
(xs , p) ++ (ys , q) = (λ zs → xs (ys zs))
  , (λ zs as → p (ys zs) as  ∙ cong xs (q zs as))

▷_ : DList A → JList A
▷_ (xs , _) = xs []

◁_ : JList A → DList A
◁_ = recJ DListIsSet
  ((λ xs → xs) , (λ _ _ → refl))
  _++_
  (λ x → [ x ] ⧺_ , ⧺-assoc [ x ])
  (λ x y z → ΣPathP (refl , funExt (λ xs → funExt (λ ys → trunc _ _ _ _))))
  (λ x → ΣPathP (refl , funExt (λ xs → funExt (λ ys → trunc _ _ _ _))))
  (λ x → ΣPathP (refl , funExt (λ xs → funExt (λ ys → trunc _ _ _ _))))

▷◁ : (xs : JList A) → ▷ ◁ xs ≡ xs
▷◁ xs = elimJProp (λ xs → trunc (▷ ◁ xs) xs) refl
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
  (λ a → ⧺-idʳ [ a ]) xs

◁≡→≡ : {xs ys : JList A} → (◁ xs) .fst ≡ (◁ ys) .fst → xs ≡ ys
◁≡→≡ p = sym (▷◁ _) ∙ (λ i → p i []) ∙ ▷◁ _

example
  : {x : A} (xs ys zs : JList A)
  → [ x ] ⧺ xs ⧺ ([] ⧺ ys ⧺ zs) ≡ [ x ] ⧺ (xs ⧺ ys) ⧺ [] ⧺ zs
example xs ys zs = ◁≡→≡ refl
-- the underlying idea is that we can normalise the expression with
-- repect to functional presentation


{-
module _ {A B : Set} (BisSet : isSet B) (e : B) (_*_ : B → B → B) (i : A → B)
  (assoc : ∀ x y z → (x * y) * z ≡ x * (y * z))
  (idʳ : ∀ x → x * e ≡ x)
  (idˡ : ∀ x → e * x ≡ x) where

  recJ : JList A → B
  recJ []        = e
  recJ (xs ⧺ ys) = recJ xs * recJ ys
  recJ [ x ]     = i x
  recJ (⧺-assoc xs ys zs i) = assoc (recJ xs) (recJ ys) (recJ zs) i
  recJ (⧺-idʳ xs i) = idʳ (recJ xs) i
  recJ (⧺-idˡ xs i) = idˡ (recJ xs) i
  recJ (trunc xs ys p q i j) =
    isSet→SquareP (λ _ _ → BisSet) (cong recJ p) (cong recJ q) refl refl i j

  module _ {P : B → Set} (PisSet : ∀ x → isSet (P x))
    (pe : P e) (_*P_ : ∀ {x y} → P x → P y → P (x * y)) (iP : ∀ a → P (i a))
    (assocP : {x y z : B}(px : P x)(py : P y)(pz : P z) →
      PathP (λ i → P (assoc x y z i)) ((px *P py) *P pz) (px *P (py *P pz)))
    (idʳP : {x : B}(px : P x) → PathP (λ i → P (idʳ x i)) (px *P pe) px)
    (idˡP : {x : B}(px : P x) → PathP (λ i → P (idˡ x i)) (pe *P px) px)
    where

    elimJ : (xs : JList A) → P (recJ xs)
    elimJ []        = pe
    elimJ (xs ⧺ ys) = elimJ xs *P elimJ ys
    elimJ [ x ]     = iP x
    elimJ (⧺-assoc xs ys zs i) = assocP (elimJ xs) (elimJ ys) (elimJ zs) i
    elimJ (⧺-idʳ xs i) = idʳP (elimJ xs) i
    elimJ (⧺-idˡ xs i) = idˡP (elimJ xs) i
    elimJ (trunc xs ys p q i j) = 
      isOfHLevel→isOfHLevelDep 2 (λ x → PisSet (recJ x)) (elimJ xs) (elimJ ys) (cong elimJ p) (cong elimJ q) (trunc xs ys p q) i j

  module _ {P : B → Set} (PisProp : ∀ x → isProp (P x))
    (pe : P e) (_*P_ : ∀ {x y} → P x → P y → P (x * y)) (iP : ∀ a → P (i a))
    where

    elimJProp : (xs : JList A) → P (recJ xs)
    elimJProp = elimJ (λ x → isProp→isSet (PisProp x))
      pe _*P_ iP (λ _ _ _ → toPathP (PisProp _ _ _)) (λ _ → toPathP (PisProp _ _ _)) (λ _ → toPathP (PisProp _ _ _))

initial
  : (xs : JList A)
  → recJ trunc [] _⧺_ [_] ⧺-assoc ⧺-idʳ ⧺-idˡ xs ≡ xs
initial = elimJProp' (λ xs → trunc _ _) refl (λ p q → cong₂ _⧺_ p q) (λ a → refl)

-}

-- -- -- -- data ∥_∥ (A : Set) : Prop where
-- -- -- --   ∣_∣ : A → ∥ A ∥
-- -- -- -- 
-- -- -- -- rec : {A : Set} {B : Prop} → (A → B) → ∥ A ∥ → B
-- -- -- -- rec f ∣ x ∣ = f x
-- -- -- -- 
-- -- -- -- rec2 : {A B : Set} {C : Prop} → (A → B → C) → ∥ A ∥ → ∥ B ∥ → C
-- -- -- -- rec2 f ∣ x ∣ ∣ y ∣ = f x y

-- -- -- -- record Σp (A : Set) (B : A → Prop) : Set where
-- -- -- --   constructor _,_
-- -- -- --   field
-- -- -- --     fst : A
-- -- -- --     snd : B fst
-- -- -- -- open Σp public
-- -- -- -- 
-- -- -- -- infixr 4 _,_
-- -- -- -- 
-- -- -- -- Σp-syntax : (A : Set) (B : A → Prop) → Set
-- -- -- -- Σp-syntax = Σp
-- -- -- -- 
-- -- -- -- syntax Σp-syntax A (λ x → B) = Σp[ x ∈ A ] B

-- -- -- -- data List (A : Set) : Set where
-- -- -- --   []  : List A
-- -- -- --   _∷_ : A → List A → List A

-- -- -- -- _++_ : List A → List A → List A
-- -- -- -- []       ++ ys = ys
-- -- -- -- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- -- -- -- infixr 10 _++_ _++'_

-- -- -- -- ++-identityʳ : (xs : List A) → xs ++ [] ≡ xs
-- -- -- -- ++-identityʳ []       = refl
-- -- -- -- ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- -- -- -- ++-assoc
-- -- -- --   : (xs ys zs : List A)
-- -- -- --   → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
-- -- -- -- ++-assoc []       ys zs = refl
-- -- -- -- ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

-- -- -- -- DList : Set → Set
-- -- -- -- DList A = Σp[ xs ∈ (List A → List A) ]
-- -- -- --   ∥ ((ys zs : List A) → xs ys ++ zs ≡ xs (ys ++ zs)) ∥

-- -- -- -- _++'_ : DList A → DList A → DList A
-- -- -- -- (xs , p) ++' (ys , q) = (λ zs → xs (ys zs))
-- -- -- --   , rec2 (λ p q → ∣ (λ zs as → p (ys zs) as ∙ cong xs (q zs as)) ∣) p q

-- -- -- -- []' : DList A
-- -- -- -- []' = (λ ys → ys) , ∣ (λ _ _ → refl) ∣

-- -- -- -- ++'-identityʳ : (xs : DList A) → xs ++' []' ≡ xs
-- -- -- -- ++'-identityʳ xs = refl

-- -- -- -- ++'-assoc
-- -- -- --   : (xs ys zs : DList A)
-- -- -- --   → (xs ++' ys) ++' zs ≡ xs ++' ys ++' zs
-- -- -- -- ++'-assoc xs ys zs = refl

-- -- -- -- data JList (A : Set) : Set
-- -- -- -- flatten : JList A → List A

-- -- -- -- data JList A where
-- -- -- --   []  : JList A
-- -- -- --   [_] : A → JList A
-- -- -- --   _⧺_ : JList A → JList A → JList A
-- -- -- --   nf : (xs ys : JList A) → flatten xs ≡ flatten ys → xs ≡ ys
  
-- -- -- -- flatten []        = []
-- -- -- -- flatten [ x ]     = x ∷ []
-- -- -- -- flatten (xs ⧺ ys) = flatten xs ++ flatten ys
-- -- -- -- flatten (nf xs ys x i) = x i

-- -- -- -- fromList : List A → DList A
-- -- -- -- fromList xs = (λ ys → xs ++ ys) , ∣ ++-assoc xs ∣

-- -- -- -- toList : DList A → List A
-- -- -- -- toList (xs , _) = xs []

-- -- -- -- fromJList : JList A → DList A
-- -- -- -- fromJList []        = (λ xs → xs) , ∣ (λ _ _ → refl) ∣
-- -- -- -- fromJList [ x ]     = (λ xs → x ∷ xs) , ∣ (λ _ _ → refl) ∣
-- -- -- -- fromJList (xs ⧺ ys) = fromJList xs ++' fromJList ys
-- -- -- -- fromJList (nf xs xs' p i) = {!!} -- (λ zs → {!!}) , ∣ {!λ !} ∣

-- -- -- -- postulate
-- -- -- --   toJList : DList A → JList A
-- -- -- --   toJList-fromJList
-- -- -- --     : (xs : JList A) → toJList (fromJList xs) ≡ xs
-- -- -- -- -- toJList (xs , p) = {!!}
-- -- -- -- postulate
-- -- -- --   fromList-toList : (xs : DList A) → fromList (toList xs) ≡ xs -- List needs to be a set
-- -- -- -- --  (xs []) ++_ , _
-- -- -- -- --    ≡⟨ {!!} ⟩
-- -- -- -- --  (λ ys → xs ([] ++ ys)) , p
-- -- -- -- --    ≡⟨ refl ⟩
-- -- -- -- --  xs , p
-- -- -- -- --    ∎ 

-- -- -- -- toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
-- -- -- -- toList-fromList = ++-identityʳ

-- -- -- -- fromList++
-- -- -- --   : (xs ys : List A)
-- -- -- --   → fromList (xs ++ ys) ≡ fromList xs ++' fromList ys
-- -- -- -- fromList++ xs ys i = (λ zs → ++-assoc xs ys zs i) , ∣ (λ ys zs → {!!}) ∣ -- requires that List is a set 

-- -- -- -- example
-- -- -- --   : (xs ys zs : List A)
-- -- -- --   → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
-- -- -- -- example xs ys zs =
-- -- -- --   xs ++ ys ++ zs
-- -- -- --     ≡⟨ sym $ toList-fromList _ ⟩
-- -- -- --   toList (fromList (xs ++ ys ++ zs))
-- -- -- --     ≡⟨ cong toList (fromList++ xs (ys ++ zs)) ⟩
-- -- -- --   toList (fromList xs ++' (fromList (ys ++ zs)))
-- -- -- --     ≡⟨ cong toList (cong (fromList xs ++'_) (fromList++ ys zs)) ⟩
-- -- -- --   toList (fromList xs ++' (fromList ys ++' fromList zs))
-- -- -- --     ≡⟨ refl ⟩
-- -- -- --   toList ((fromList xs ++' fromList ys) ++' fromList zs)
-- -- -- --     ≡⟨ cong toList (cong (_++' fromList zs) (sym $ fromList++ xs ys)) ⟩
-- -- -- --   toList (fromList (xs ++ ys) ++' fromList zs)
-- -- -- --     ≡⟨ cong toList (sym $ fromList++ (xs ++ ys) zs) ⟩
-- -- -- --   toList (fromList ((xs ++ ys) ++ zs))
-- -- -- --     ≡⟨ toList-fromList _ ⟩
-- -- -- --   (xs ++ ys) ++ zs
-- -- -- --     ∎

-- -- -- -- example2
-- -- -- --   : (xs ys zs : JList A)
-- -- -- --   → xs ⧺ (ys ⧺ zs) ≡ (xs ⧺ ys) ⧺ zs
-- -- -- -- example2 xs ys zs =
-- -- -- --     sym (toJList-fromJList (xs ⧺ (ys ⧺ zs)))
-- -- -- -- --  ∙ cong toJList lemma
-- -- -- --   ∙ toJList-fromJList ((xs ⧺ ys) ⧺ zs) 
-- -- -- --   where
-- -- -- --     lemma : fromJList (xs ⧺ (ys ⧺ zs)) ≡ fromJList ((xs ⧺ ys) ⧺ zs)
-- -- -- --     lemma = refl
