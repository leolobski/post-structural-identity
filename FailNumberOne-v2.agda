--人生の痛み
--{-# OPTIONS --without-K #-}
--{-# OPTIONS --type-in-type #-}

--open import lib.Base
--open import lib.PathGroupoid
--open import Naturals
open import Bool
open import PropositionsAsTypes
--open import 2DependentTypes
--open import 3DependentTypes2
open import Equality

module FailNumberOne-v2 where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

module _  {X Y : Set } (f : X → Y) where
  record qinv : Set  where
    field
      g : Y → X
      f-g : (y : Y) → (f (g y) == y)
      g-f : (x : X) → (g (f x) == x)

module Σ-stuff {A : Set} {B : A → Set} where --this is copied from a sheet we did in class

  {- The first step is to define a relation on Σ A B that should be equivalent
     to the identity type. For this we will use the record type Σ-eq below.
  -}
  record Σ-eq (ab ab' : Σ A B) : Set where
    constructor Σ-eq-in
    field
      fst-eq : Σ.fst ab == Σ.fst ab'
      snd-eq : (transport B fst-eq (Σ.snd ab)) == Σ.snd ab'
        {- note that Σ.snd ab == Σ.snd ab' would not be a well defined type
          since Σ.snd ab and Σ.snd ab' have different types -}

  {- The encode function maps from the real equality type into the new relation. -}
  encode : (ab ab' : Σ A B) → (ab == ab') → Σ-eq ab ab'
  encode ab .ab idp = Σ-eq-in idp idp


  {- We aim to find a quasi inverse for encode ab ab' for each ab and ab'. -}

  {- The underlying function g will be the function decode below. -}
  decode : (ab ab' : Σ A B) → (Σ-eq ab ab') → ab == ab'
  decode (fst , snd) (.fst , .snd) (Σ-eq-in idp idp) = idp

  {- We now need to check that this does give a quasi inverse. -}
  f-g : (ab ab' : Σ A B) → (x : Σ-eq ab ab') → encode ab ab' (decode ab ab' x) == x
  f-g (fst , snd) (.fst , .snd) (Σ-eq-in idp idp) = idp

  g-f : (ab ab' : Σ A B) → (p : ab == ab') → (decode ab ab' (encode ab ab' p) == p)
  g-f (fst , snd) (.fst , .snd) idp = idp

  {- Finally we package everything together to get an element of qinv (encode ab ab')
     for each ab and ab'.
  -}
  Σ-eq-qinv : (ab ab' : Σ A B) → (qinv (encode ab ab'))
  Σ-eq-qinv ab ab' = record {g = decode ab ab' ; f-g = f-g ab ab' ; g-f = g-f ab ab'}

-- _∘_ : (a b c : A₀) (A₁ b c) (A₁ a b) → (A₁ a c)
-- f ∘ g = comp f g

-- data _==_ {X : Set} (x : X) : X → Set where
--  idp : x == x

is-hprop : Set → Set
is-hprop X = (x y : X) → (x == y)

{- An h-set is a type where every identity type is an h-proposition. -}
is-hset : Set → Set
is-hset X = (x y : X) → is-hprop (x == y)

------------------------------------------------------------------------------------------------------------------------------------------------

-- definition of precategory
record pcat : Set₁ where
  field
    A₀ : Set    -- X is the set of vector spaces, A₀ is a vector space
    A₁ : A₀ → A₀ → Set   -- A₁ x y = Hom (x, y)
    A₁-is-hset : (a : A₀) → (b : A₀) → is-hset (A₁ a b)
    id : {a : A₀} → (A₁ a a)   -- id a is an element of Hom (a, a)
    _∘_ : {a b c : A₀} → (A₁ b c) → (A₁ a b) → (A₁ a c) -- composition
    ur : {a b : A₀} → (f : A₁ a b) → f == (f ∘ id)
    ul : {a b : A₀} → (f : A₁ a b) → f == (id ∘ f)
    α : {a b c d : A₀} → (f : A₁ a b) → (g : A₁ b c) → (h : A₁ c d) → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f) -- associativity

record iso (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) : Set where  -- isomorphism
  field
    g : pcat.A₁ C b a   -- inverse map
    τ : pcat._∘_ C g f == pcat.id C   --left inverse witness
    ε : pcat._∘_ C f g == pcat.id C   --right inverse witness



-- data _≅_ (C : pcat) (a b : pcat.A₀ C) : Set where
--  witness : Σ (pcat.A₁ C a b) (λ f → iso C f)

-- _≅_ : (C : pcat) (a b : pcat.A₀ C) → (w : Σ (pcat.A₁ C a b) (λ f → iso C f)) → Σ.fst w

-- postulate
--  F : (a ≅ b) → pcat.A₁ a b →

--  data _==_ {X : Set} (x : X) : X → Set where
--  idp : x == x -- idp is short for "identity path". The HoTT book says refl instead.

--  postulate
--  homset-is-hset : {C :  pcat} {a b : pcat.A₀ C} → is-hset ( pcat.A₁ C a b ) -- But since all hom-sets are sets...
--  homset-is-hset = λ x y z w → {!   !}

--postulate
--  eq-inverse-implies-eq-iso : (C : pcat) {a b : pcat.A₀ C} → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)

eq-inverse-implies-eq-iso : (C : pcat) {a b : pcat.A₀ C} → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)
eq-inverse-implies-eq-iso C f record { g = g ; τ = τ ; ε = ε } record { g = .g ; τ = τ₁ ; ε = ε₁ } idp = ap (λ x → record{ g = g ; τ = iso.τ x ; ε = iso.ε x}) idp

--eq-inverse-implies-eq-iso' : (C : pcat) {a b : pcat.A₀ C} → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)
--eq-inverse-implies-eq-iso' = {!   !}

-- Lemma 9.1.3
is-iso-is-hprop : (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) → is-hprop (iso C f)
is-iso-is-hprop C f = λ i j → eq-inverse-implies-eq-iso C f i j (pcat.ul C (iso.g i)
 ∙ (ap (λ x → pcat._∘_ C x (iso.g i)) (! (iso.τ j)) ∙ ( ! (pcat.α C (iso.g i) f (iso.g j))
 ∙ (ap (λ x → pcat._∘_ C (iso.g j) x) (iso.ε i) ∙ ! (pcat.ur C (iso.g j)) ))))

 -- Lemma 9.1.4
id-to-iso : (C : pcat) {a b : pcat.A₀ C} (p : a == b) → (Σ (pcat.A₁ C a b) (λ f → iso C f))
id-to-iso C idp = (pcat.id C) , (record { g = pcat.id C ; τ = ! (pcat.ur C (pcat.id C)) ; ε = ! (pcat.ur C (pcat.id C)) })

record is-hae {X Y : Set} (f : X → Y) : Set where
    field
      g : Y → X
      f-g : (y : Y) → (f (g y) == y)
      g-f : (x : X) → (g (f x) == x)
      --adj : (x : X) → ap f (g-f x) == f-g (f x)

-- Definition of a category
record cat : Set₁ where
  field
    precat : pcat
    iso-to-id :  {a b : pcat.A₀ precat} → (f : pcat.A₁ precat a b) → (p : iso precat f) → (a == b)
    wit-hae : {a b : pcat.A₀ precat} → is-hae (id-to-iso precat {a} {b})
    --wit-hae' : {a b : pcat.A₀ precat} → is-hae {a == b} {Σ (pcat.A₁ precat a b) (λ f → iso precat f)} (id-to-iso precat)

is-cat : (X : pcat) → Set
is-cat X =  {a b : pcat.A₀ X} → (f : pcat.A₁ X a b) → (p : iso X f) → (a == b)


-- Definition 9.8.1

record str (X : pcat) : Set₁ where -- notion of structure over a precategory X
  field
    P : pcat.A₀ X → Set -- interpretation
    H : {x y : pcat.A₀ X} {α : P x} {β : P y} (f : pcat.A₁ X x y) → Set -- homomorphism of structures
    H-is-hprop : {x y : pcat.A₀ X} {α : P x} {β : P y} (f : pcat.A₁ X x y) → is-hprop (H f)
    H-id : {x : pcat.A₀ X} {α : P x} → H (pcat.id X)
    H-comp : {x y z : pcat.A₀ X} {α : P x} {β : P y} {γ : P z}  (f : pcat.A₁ X y z) → (g : pcat.A₁ X x y) →
      (H f) → (H g) → (H (pcat._∘_ X f g))
    --leq : (x : pcat.A₀ X) → (α β : P x) → Set
    --leq x α β = H (pcat.id X x)

H-lemma : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → (g : pcat.A₁ X y z) → (f == g) → str.H S f → str.H S g
H-lemma X S f .f idp = λ z → z

-- left unit for a structure homomorphism
H-ul : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S f → str.H S (pcat._∘_ X (pcat.id X) f)
H-ul = λ X S {y} {z} {β} {γ} f → str.H-comp S (pcat.id X) f (str.H-id S)

H-ul-inv : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S (pcat._∘_ X (pcat.id X) f) → str.H S f
H-ul-inv X S {y} {z} {β} {γ} f w = H-lemma X S (pcat._∘_ X (pcat.id X) f) f (! (pcat.ul X f)) w

-- right unit for a structure homomorphism
H-ur : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S f → str.H S (pcat._∘_ X f (pcat.id X))
H-ur = λ X S {y} {z} {β} {γ} f z₁ → str.H-comp S f (pcat.id X) z₁ (str.H-id S)

--H-ur' : (X : pcat) → (S : str X) {y z : pcat.A₀ X}{β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) →
--          (str.H S f  == str.H S (pcat._∘_ X f (pcat.id X)))
--H-ur' X S {y} {z} {β} {γ} f = ap (λ g → str.H S g) (pcat.ur X f)

--H-ur' : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → (w : str.H S f) →
--      transport (λ v → str.H S v) (pcat.ur X f) w == str.H-comp S f (pcat.id X) w (str.H-id S)
--H-ur' X S {y} {z} {β} {γ} f w = ap {pcat.A₁ X y z} {?} ? {pcat._∘_ X f (pcat.id X)} {f} (! (pcat.ur X f))

H-ur-inv : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S (pcat._∘_ X f (pcat.id X)) → str.H S f
H-ur-inv X S {y} {z} {β} {γ} f w = H-lemma X S (pcat._∘_ X f (pcat.id X)) f (! (pcat.ur X f)) w

-- Order on the interpretation of an object
leq : (X : pcat) → (S : str X) → (x : pcat.A₀ X) → (α β : str.P S x) → Set
leq X S x α β = str.H S {x} {x} {α} {β} (pcat.id X)

-- Standard notion of structure
record stdstr (X : pcat) : Set₁ where
  field
    S : str X
    spleq : (x : pcat.A₀ X) → (α β : str.P S x) → (leq X S x α β ) → (leq X S x β α) → (α == β)


leo-r : (X : pcat) → (S : str X) → {x y : pcat.A₀ X} (f : pcat.A₁ X x y) → (snd : str.H S f) →
  transport (λ v → str.H S v) (pcat.ur X f) snd == str.H-comp S f (pcat.id X) snd (str.H-id S)
leo-r X S f snd = ap (λ z → str.H-comp S {!  !} (pcat.id X) {!   !} (str.H-id S)) (Σ-stuff.decode (f , snd) (f , snd) (Σ-stuff.Σ-eq-in idp idp))

leo-l : (X : pcat) → (S : str X) → {x y : pcat.A₀ X} (f : pcat.A₁ X x y) → (snd : str.H S f) →
  transport (λ v → str.H S v) (pcat.ul X f) snd == str.H-comp S (pcat.id X) f (str.H-id S) snd
leo-l X S f snd = ap (λ z → str.H-comp S (pcat.id X) f (str.H-id S) snd) (Σ-stuff.decode (f , snd) (f , snd) (Σ-stuff.Σ-eq-in idp idp))

leo-α : (X : pcat) → (S : str X) → {x y z w : pcat.A₀ X} (f : pcat.A₁ X x y) → (g : pcat.A₁ X y z) → (h : pcat.A₁ X z w) → (H-f : str.H S f) → (H-g : str.H S g) → (H-h : str.H S h) →
  transport (λ v → str.H S v) (pcat.α X f g h) (str.H-comp S h (pcat._∘_ X g f) H-h (str.H-comp S g f H-g H-f)) == (str.H-comp S (pcat._∘_ X h g) f (str.H-comp S h g H-h H-g) H-f)
leo-α X S f g h H-f H-g H-h = ap (λ x → str.H-comp S (pcat._∘_ X h g) f (str.H-comp S h g H-h H-g) H-f) idp

--postulate --left as an exercise to the unfortunate reader
--  leo-r : (X : pcat) → (S : str X) → {x y : pcat.A₀ X} (f : pcat.A₁ X x y) → (snd : str.H S f) →
--    transport (λ v → str.H S v) (pcat.ur X f) snd == str.H-comp S f (pcat.id X) snd (str.H-id S)-
--  leo-l : (X : pcat) → (S : str X) → {x y : pcat.A₀ X} (f : pcat.A₁ X x y) → (snd : str.H S f) →
--    transport (λ v → str.H S v) (pcat.ul X f) snd == str.H-comp S (pcat.id X) f (str.H-id S) snd
--  leo-α : (X : pcat) → (S : str X) → {x y z w : pcat.A₀ X} (f : pcat.A₁ X x y) → (g : pcat.A₁ X y z) → (h : pcat.A₁ X z w) → (H-f : str.H S f) → (H-g : str.H S g) → (H-h : str.H S h) →
--    transport (λ v → str.H S v) (pcat.α X f g h) (str.H-comp S h (pcat._∘_ X g f) H-h (str.H-comp S g f H-g H-f)) == (str.H-comp S (pcat._∘_ X h g) f (str.H-comp S h g H-h H-g) H-f)

--transport-lemma : (X : pcat) → (S : stdstr X) → (a b : pcat.A₀ X) → (p : a == b) → (α : str.P (stdstr.S S) a) → (β : str.P (stdstr.S S) b) →
--  (transport (str.P (stdstr.S S)) p α) == β
--transport-lemma X S a .a idp α β = stdstr.spleq S a α β (str.H-id (stdstr.S S)) (str.H-id (stdstr.S S))

transport-lemma : (X : cat) → (S : stdstr (cat.precat X)) → (a b : pcat.A₀ (cat.precat X)) → (p : a == b) → (α : str.P (stdstr.S S) a) → (β : str.P (stdstr.S S) b) → (s : str.H (stdstr.S S) {a} {b} {α} {β} (Σ.fst (id-to-iso (cat.precat X) p))) → (t : str.H (stdstr.S S) {b} {a} {β} {α} (Σ.fst (id-to-iso (cat.precat X) (! p)))) →
  (transport (str.P (stdstr.S S)) p α) == β
transport-lemma X S a .a idp α β s t = stdstr.spleq S a α β s t

-- Precategory of structures
pcatstr : (X : pcat) → (S : str X) → pcat
pcatstr X S =
  record { A₀ = Σ  (pcat.A₀ X) (str.P S) ;
    A₁ = λ {(x , α) (y , β) → Σ (pcat.A₁ X x y) λ f → str.H S f} ;
    A₁-is-hset = λ { a b x .x idp idp → idp} ; --λ { a b x .x idp idp → idp} this doesn't work without κ !!!
    id = (pcat.id X , str.H-id S) ;
    _∘_ = λ { (fst , snd) (fst₁ , snd₁) → (pcat._∘_ X fst fst₁) , str.H-comp S fst fst₁ snd snd₁} ;
    ur = λ {(f , snd) → Σ-stuff.decode (f , snd) ((pcat._∘_ X f (pcat.id X)) , str.H-comp S f (pcat.id X) snd (str.H-id S))
        (Σ-stuff.Σ-eq-in (pcat.ur X f) (leo-r X S f snd) )} ;
    ul = λ {(f , snd) → Σ-stuff.decode (f , snd) ((pcat._∘_ X (pcat.id X) f) , str.H-comp S (pcat.id X) f (str.H-id S) snd)
        (Σ-stuff.Σ-eq-in (pcat.ul X f) (leo-l X S f snd) )} ;
    α = λ {(f , H-f) (g , H-g) (h , H-h) → Σ-stuff.decode ((pcat._∘_ X h (pcat._∘_ X g f))
      , str.H-comp S h (pcat._∘_ X g f) H-h (str.H-comp S g f H-g H-f)) ((pcat._∘_ X (pcat._∘_ X h g) f) ,
      (str.H-comp S (pcat._∘_ X h g) f (str.H-comp S h g H-h H-g) H-f)) (Σ-stuff.Σ-eq-in
        (pcat.α X f g h) (leo-α X S f g h H-f H-g H-h)) }


      -- This is shit !
      {-    let
         id = λ {a} → (pcat.id X {a}) , (str.H-id S {a})
        _∘_ = λ {a} {b} {c} → λ { (fst , snd) (fst₁ , snd₁) → (pcat._∘_ X {a} {b} {c} fst fst₁) , str.H-comp {a} {b} {c} S fst fst₁ snd snd₁}
       in-} }

{- postulate
  leo-thm : (X : cat) → (S : stdstr (cat.precat X)) → (PCS : pcatstr (cat.precat X) (stdstr.S S)) →
    {a b : pcat.A₀ PCS} → (f : pcat.A₁ a b) → (f-uck : iso PCS f) →
    (transport (λ v → str.P (stdstr.S S) v) (cat.iso-to-id X (Σ.fst f)
    (record { g = Σ.fst (iso.g f-uck) ;
    τ = ap Σ.fst (iso.τ f-uck) ;
    ε = ap Σ.fst (iso.ε f-uck) })) (Σ.snd a)) == Σ.snd b -}
-- THE THEOREM !!!!!!

str-id-ppl : (X : cat) → (S : stdstr (cat.precat X)) → is-cat (pcatstr (cat.precat X) (stdstr.S S))
str-id-ppl X S {fst , snd} {fst₁ , snd₁} f f-uck =
  Σ-stuff.decode (fst , snd) (fst₁ , snd₁) (Σ-stuff.Σ-eq-in (cat.iso-to-id X (Σ.fst f)
  (record { g = Σ.fst (iso.g f-uck) ; τ = ap (λ x → Σ.fst x) (iso.τ f-uck) ; ε = ap (λ x → Σ.fst x) (iso.ε f-uck) }))
  (transport-lemma X S fst fst₁ (cat.iso-to-id X (Σ.fst f)  (record { g = Σ.fst (iso.g f-uck) ; τ = ap (λ x → Σ.fst x) (iso.τ f-uck) ; ε = ap (λ x → Σ.fst x) (iso.ε f-uck) })) snd snd₁ {!  !} {!  !} ))

{-  str.H (stdstr.S S)
      (Σ.fst
       (id-to-iso (cat.precat X)
        (cat.iso-to-id X (Σ.fst f)
         (record
          { g = Σ.fst (iso.g f-uck)
          ; τ = ap Σ.fst (iso.τ f-uck)
          ; ε = ap Σ.fst (iso.ε f-uck)
          })))) -}

record magma (A : Set) : Set where
  field
    _*_ : A → A → A

record monoid (A : Set) : Set where
  field
    _*_ : A → A → A
    m_unit : A
    ur : (a : A) → (a == (a * m_unit))
    ul : (a : A) → (a == (m_unit * a))
