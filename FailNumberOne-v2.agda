--人生の痛み

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

module Σ-stuff {A : Set} {B : A → Set} where

  {- The first step is to define a relation on Σ A B that should be equivalent
     to the identity type. For this we will use the record type Σ-eq below.
  -}
  record Σ-eq (ab ab' : Σ A B) : Set where
    constructor Σ-eq-in
    field
      fst-eq : Σ.fst ab == Σ.fst ab'
      snd-eq : (transport {A} B fst-eq (Σ.snd ab)) == Σ.snd ab'
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
    id : (a : A₀) → (A₁ a a)   -- id a is an element of Hom (a, a)
    _∘_ : {a b c : A₀} → (A₁ b c) → (A₁ a b) → (A₁ a c) -- composition
    ur : {a b : A₀} → (f : A₁ a b) → f == (f ∘ id a)
    ul : {a b : A₀} → (f : A₁ a b) → f == (id b ∘ f)
    α : {a b c d : A₀} → (f : A₁ a b) → (g : A₁ b c) → (h : A₁ c d) → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f) -- associativity

record iso (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) : Set where  -- isomorphism
  field
    g : pcat.A₁ C b a   -- inverse map
    τ : pcat._∘_ C g f == pcat.id C a   --left inverse witness
    ε : pcat._∘_ C f g == pcat.id C b   --right inverse witness



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

postulate
  eq-inverse-implies-eq-iso : (C : pcat) {a b : pcat.A₀ C} → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)

eq-inverse-implies-eq-iso' : (C : pcat) {a b : pcat.A₀ C} → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)
eq-inverse-implies-eq-iso' = {!   !}

-- Lemma 9.1.3
is-iso-is-hprop : (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) → is-hprop (iso C f)
is-iso-is-hprop C f = λ i j → eq-inverse-implies-eq-iso C f i j (pcat.ul C (iso.g i)
 ∙ (ap (λ x → pcat._∘_ C x (iso.g i)) (! (iso.τ j)) ∙ ( ! (pcat.α C (iso.g i) f (iso.g j))
 ∙ (ap (λ x → pcat._∘_ C (iso.g j) x) (iso.ε i) ∙ ! (pcat.ur C (iso.g j)) ))))

 -- Lemma 9.1.4
if-id-then-iso : (C : pcat) (a b : pcat.A₀ C) (p : a == b) → (Σ (pcat.A₁ C a b) (λ f → iso C f))
if-id-then-iso C a .a idp = (pcat.id C a) , (record { g = pcat.id C a ; τ = ! (pcat.ur C (pcat.id C a)) ; ε = ! (pcat.ur C (pcat.id C a)) })

-- Definition of a category
record cat : Set₁ where
  field
    precat : pcat
    iso-to-id :  {a b : pcat.A₀ precat} → (f : pcat.A₁ precat a b) → (p : iso precat f) → (a == b)

-- Definition 9.8.1

record str (X : pcat) : Set₁ where -- notion of structure over a precategory X
  field
    P : pcat.A₀ X → Set -- interpretation
    H : (x y : pcat.A₀ X) → (α : P x) → (β : P y) → (f : pcat.A₁ X x y) → Set -- homomorphism of structures
    H-is-hprop : {x y : pcat.A₀ X} {α : P x} {β : P y} (f : pcat.A₁ X x y) → is-hprop (H x y α β f)
    H-id : (x : pcat.A₀ X) (α : P x) → H x x α α (pcat.id X x)
    H-comp : {x y z : pcat.A₀ X} {α : P x} {β : P y} {γ : P z}  (f : pcat.A₁ X y z) → (g : pcat.A₁ X x y) →
      ((H y z β γ f) → (H x y α β g) → (H x z α γ (pcat._∘_ X f g)))
    --leq : (x : pcat.A₀ X) → (α β : P x) → Set
    --leq x α β = H x x α β (pcat.id X x)

-- Order on the interpretation of an object
leq : (X : pcat) → (S : str X) → (x : pcat.A₀ X) → (α β : str.P S x) → Set
leq X S x α β = str.H S x x α β (pcat.id X x)

-- Standard notion of structure
record stdstr (X : pcat) : Set₁ where
  field
    S : str X
    spleq : (x : pcat.A₀ X) → (α β : str.P S x) → (leq X S x α β ) → (leq X S x β α) → (α == β)

-- Precategory of structures
pcatstr : (X : pcat) → (S : str X) → pcat
pcatstr  record { A₀ = A₀ ; A₁ = A₁ ; A₁-is-hset = A₁-is-hset ; id = id ; _∘_ = _∘_ ; ur = ur ; ul = ul ; α = α } record { P = P ; H = H ; H-is-hprop = H-is-hprop ; H-id = H-id ; H-comp = H-comp } =
  record { A₀ = Σ  A₀ P ;
    A₁ = λ {(x , α) (y , β) → Σ (A₁ x y) λ f → H x y α β f} ;
    A₁-is-hset = λ { a b x .x idp idp → idp} ;
    id = λ {(x , α) → (id x) , H-id x α} ;
    _∘_ = λ { (fst , snd) (fst₁ , snd₁) → (fst ∘ fst₁) , H-comp fst fst₁ snd snd₁} ;
    ur = λ {(f , snd) → Σ-stuff.decode (f , snd) (( f ∘ (id _)) , H-comp f (id _) snd (H-id _ _))
      (Σ-stuff.Σ-eq-in (ur f) ( H-is-hprop (f ∘ id _) {! _ !} (H-comp f (id _) snd (H-id _ _) )))} ;
    ul = {!   !} ;
    α = {!   !} }

{- H (Σ.fst .a) (Σ.fst .b) (Σ.snd .a) (Σ.snd .b)
      (f ∘ id (Σ.fst .a)) -}
