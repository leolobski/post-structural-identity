--人生の痛み

--open import Naturals
--open import Bool
--open import DependentTypes
--open import DependentTypes2
open import Equality

module FailNumberOne where

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

record iso {C : pcat} {a b : pcat.A₀ C} (f : pcat.A₁ C a b) : Set where  -- isomorphism
  field
    g : pcat.A₁ C b a   -- inverse map
    τ : pcat._∘_ C g f == pcat.id C a   --left inverse witness
    ε : pcat._∘_ C f g == pcat.id C b   --right inverse witness

--postulate
  --homset-is-hset : {C : pcat} {a b : pcat.A₀ C} → is-hset ( pcat.A₁ C a b ) -- But since all hom-sets are sets...

leo : {C : pcat} {a b : pcat.A₀ C} (f : pcat.A\_1 C a b) → ( i j : iso f) → (p : iso.g i == iso.g j) → (q : i == j)
leo = ?
  --  homset-is-hset = λ x y z w → {!   !}

is-iso-is-hprop : {C : pcat} {a b : pcat.A₀ C} (f : pcat.A₁ C a b) → is-hprop (iso f) -- Lemma 9.1.3
--is-iso-is-hprop f = λ g' g → pcat.ul {!  !} (iso.g g') ∙ ( ap (λ x → pcat._∘_ {!  !} x  g') (pcat._∘_ {!  !} (iso.τ g) f) ∙ ( pcat.ur {!   !} (iso.g g') ∙ ( ! (pcat.α {!    !} g f g') ∙ ! (pcat.ur {!   !} (iso.g g ) ) ) ) )
is-iso-is-hprop f = λ x y → {!   !}









--composition : { A₀ : Set} (C : pcat A₀) {a b c : A₀} → ((pcat.A₁ C) b c) → ((pcat.A₁ C) a b) → ((pcat.A₁ C) a c)
--composition C f g = pcat.comp C f g
