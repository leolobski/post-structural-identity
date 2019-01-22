--人生の痛み

--open import Naturals
--open import Bool
--open import DependentTypes
--open import DependentTypes2
open import Equality

module FailNumberOne-v2 where

--_∘_ : (a b c : A₀) (A₁ b c) (A₁ a b) → (A₁ a c)
--f ∘ g = comp f g

--data _==_ {X : Set} (x : X) : X → Set where
--  idp : x == x

is-hprop : Set → Set
is-hprop X = (x y : X) → (x == y)

{- An h-set is a type where every identity type is an h-proposition. -}
is-hset : Set → Set
is-hset X = (x y : X) → is-hprop (x == y)

record pcat : Set₁ where -- definition of precategory
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

--postulate
--  homset-is-hset : {C : pcat} {a b : pcat.A₀ C} → is-hset ( pcat.A₁ C a b ) -- But since all hom-sets are sets...
--  homset-is-hset = λ x y z w → {!   !}


postulate
  eq-inverse-implies-eq-iso : (C : pcat) {a b : pcat.A₀ C} → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)

-- Lemma 9.1.3
is-iso-is-hprop : (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) → is-hprop (iso C f)
is-iso-is-hprop C f = λ i j → eq-inverse-implies-eq-iso C f i j (pcat.ul C (iso.g i)
 ∙ (ap (λ x → pcat._∘_ C x (iso.g i)) (! (iso.τ j)) ∙ ( ! (pcat.α C (iso.g i) f (iso.g j))
 ∙ (ap (λ x → pcat._∘_ C (iso.g j) x) (iso.ε i) ∙ ! (pcat.ur C (iso.g j)) ))))

 --Lemma 9.1.4

--ap
