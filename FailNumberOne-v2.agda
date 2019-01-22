--人生の痛み

--open import Naturals
open import Bool
open import PropositionsAsTypes
--open import 2DependentTypes
--open import DependentTypes2
open import Equality

module FailNumberOne-v2 where

-- _∘_ : (a b c : A₀) (A₁ b c) (A₁ a b) → (A₁ a c)
-- f ∘ g = comp f g

-- data _==_ {X : Set} (x : X) : X → Set where
--  idp : x == x

is-hprop : Set → Set
is-hprop X = (x y : X) → (x == y)

{- An h-set is a type where every identity type is an h-proposition. -}
is-hset : Set → Set
is-hset X = (x y : X) → is-hprop (x == y)

-- definition of precategory
record pcat : Set₁ where
  field
    A₀ : Set    -- X is the set of vector spaces, A₀ is a vector space
    A₁ : A₀ → A₀ → Set   -- A₁ x y = Hom (x, y)
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


record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

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
id-to-iso : (C : pcat) (a b : pcat.A₀ C) (p : a == b) → (pcat.A₁ C a b)
id-to-iso C  a .a idp = pcat.id C a

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
    H-is-hprop : (x y : pcat.A₀ X) → (α : P x) → (β : P y) → (f : pcat.A₁ X x y) → is-hprop (H x y α β f)
    H-id : (x : pcat.A₀ X) (α : P x) → H x x α α (pcat.id X x)
    H-comp : (x y z : pcat.A₀ X) → (α : P x) → (β : P y) → (γ : P z) →  (f : pcat.A₁ X x y) → (g : pcat.A₁ X y z) →
      ((H x y α β f) → (H y z β γ g) → (H x z α γ (pcat._∘_ X g f)))
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
pcatstr record { A₀ = X₀ ; A₁ = X₁ ; id = id ; _∘_ = _∘_ ; ur = ur ; ul = ul ; α = ass } record { P = P ; H = H ; H-is-hprop = H-is-hprop ; H-id = H-id ; H-comp = H-comp } =
  record { A₀ = Σ  X₀ (λ x → P x) ; A₁ = λ {(x , α) (y , β) → H x y α β _ } ; id = λ {(x , α) → H-id x α} ; _∘_ = λ {f g → {!λ x y → ?   !}} ; ur = {!   !} ; ul = {!   !} ; α = {!   !} }
