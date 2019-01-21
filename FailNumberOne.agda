--人生の痛み

--open import Naturals
--open import Bool
--open import DependentTypes
--open import DependentTypes2
--open import Equality

module FailNumberOne where

--_∘_ : (a b c : A₀) (A₁ b c) (A₁ a b) → (A₁ a c)
--f ∘ g = comp f g

data _==_ {X : Set} (x : X) : X → Set where
  idp : x == x

record pcat ( A₀ : Set) : Set₁ where -- definition of precategory
  field
--  A₀ : X    -- X is the set of vector spaces, A₀ is a vector space
    A₁ : A₀ → A₀ → Set   -- A₁ x y = Hom (x, y)
    id : (a : A₀) → (A₁ a a)   -- id a is an element of Hom (a, a)
    _∘_ : {a b c : A₀} → (A₁ b c) → (A₁ a b) → (A₁ a c) -- composition
    ur : {a b : A₀} → ( f : A₁ a b) → f == (f ∘ id a)
    ul : {a b : A₀} → ( f : A₁ a b) → f == (id b ∘ f)
    α : {a b c d : A₀} → (f : A₁ a b) → (g : A₁ b c) → (h : A₁ c d) → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f) -- associativity

inv : {A₀ set} (C : pcat A₀) → (pcat.A₁ C a b) → (pcat.A₁ C b a)
inv =

-- iso :
-- iso =











--composition : { A₀ : Set} (C : pcat A₀) {a b c : A₀} → ((pcat.A₁ C) b c) → ((pcat.A₁ C) a b) → ((pcat.A₁ C) a c)
--composition C f g = pcat.comp C f g
