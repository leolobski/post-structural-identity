--人生の痛み

--open import lib.Base
--open import lib.PathGroupoid
--open import Naturals
open import Bool
open import PropositionsAsTypes
--open import 2DependentTypes
--open import 3DependentTypes2
open import Equality

module FailNumberOne-pre-final-2 where

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
    id : (a : A₀) → (A₁ a a)   -- id a is an element of Hom (a, a)
    _∘_ : (a b c : A₀) → (A₁ b c) → (A₁ a b) → (A₁ a c) -- composition
    ur : (a b : A₀) → (f : A₁ a b) → f == (_∘_ a a b f (id a))
    ul : (a b : A₀) → (f : A₁ a b) → f == (_∘_ a b b (id b) f)
    α : (a b c d : A₀) → (f : A₁ a b) → (g : A₁ b c) → (h : A₁ c d) → (_∘_ a c d h (_∘_ a b c g f)) == (_∘_ a b d (_∘_ b c d  h g) f) -- associativity

record iso (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) : Set where  -- isomorphism
  field
    g : pcat.A₁ C b a   -- inverse map
    τ : pcat._∘_ C a b a g f == pcat.id C a   --left inverse witness
    ε : pcat._∘_ C b a b f g == pcat.id C b   --right inverse witness



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

postulate --we tried but there's problems with constraints
  eq-inverse-implies-eq-iso : (C : pcat) → (a b : pcat.A₀ C) → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)

--eq-inverse-implies-eq-iso : (C : pcat) → (a b : pcat.A₀ C) → (f : pcat.A₁ C a b) → ( i j : iso C f ) → (p : (iso.g i) == (iso.g j)) → (i == j)
--eq-inverse-implies-eq-iso C a b f record { g = g ; τ = τ ; ε = ε } record { g = .g ; τ = τ₁ ; ε = ε₁ } idp = ap (λ x → record{ g = g ; τ = iso.τ x ; ε = iso.ε x}) idp


-- Lemma 9.1.3
is-iso-is-hprop : (C : pcat) {a b : pcat.A₀ C} (f : pcat.A₁ C a b) → is-hprop (iso C f)
is-iso-is-hprop C {a} {b} f = λ i j → eq-inverse-implies-eq-iso C a b f i j (pcat.ul C b a (iso.g i)
 ∙ (ap (λ x → pcat._∘_ C b a a x (iso.g i)) (! (iso.τ j)) ∙ ( ! (pcat.α C b a b a (iso.g i) f (iso.g j))
 ∙ (ap (λ x → pcat._∘_ C b b a (iso.g j) x) (iso.ε i) ∙ ! (pcat.ur C b a (iso.g j)) ))))

 -- Lemma 9.1.4
id-to-iso : (C : pcat) {a b : pcat.A₀ C} (p : a == b) → (Σ (pcat.A₁ C a b) (λ f → iso C f))
id-to-iso C {a} {b} idp = (pcat.id C a) , (record { g = pcat.id C a ; τ = ! (pcat.ur C a b (pcat.id C a)) ; ε = ! (pcat.ur C a b (pcat.id C a)) })

record is-hae {X Y : Set} (f : X → Y) : Set where --not quite half adjoint but enough for the theorem
    field
      g : Y → X
      f-g : (y : Y) → (f (g y) == y)
      g-f : (x : X) → (g (f x) == x)
      adj : (x : X) → ap f (g-f x) == f-g (f x)

-- Definition of a category
record cat : Set₁ where
  field
    precat : pcat
    wit-hae : {a b : pcat.A₀ precat} → is-hae (id-to-iso precat {a} {b})

--iso-to-id :  (X : cat) → {a b : pcat.A₀ (cat.precat X)} → (f : pcat.A₁ (cat.precat X) a b) → (p : iso (cat.precat X) f) → (a == b)
--iso-to-id X f p = is-hae.g (cat.wit-hae X) (f , p)

iso-to-id : (X : cat) → {a b : pcat.A₀ (cat.precat X)} → Σ (pcat.A₁ (cat.precat X) a b) (λ f → iso (cat.precat X) f) → (a == b)
iso-to-id X f = is-hae.g (cat.wit-hae X) (Σ.fst f , Σ.snd f)
    --wit-hae : is-hae (id-to-iso precat)
    --wit-hae' : {a b : pcat.A₀ precat} → is-hae {a == b} {Σ (pcat.A₁ precat a b) (λ f → iso precat f)} (id-to-iso precat)
--is-cat : (X : pcat) → Set
--is-cat X =  {a b : pcat.A₀ X} → (f : pcat.A₁ X a b) → (p : iso X f) → (a == b)
iso-to-id-hae : (C : cat) → (a b : pcat.A₀ (cat.precat C)) → is-hae.g (cat.wit-hae C {a} {b}) == iso-to-id C {a} {b}
iso-to-id-hae C a b = idp

-- Definition 9.8.1

record str (X : pcat) : Set₁ where -- notion of structure over a precategory X
  field
    P : pcat.A₀ X → Set -- interpretation
    H : (x y : pcat.A₀ X) (α : P x) (β : P y) (f : pcat.A₁ X x y) → Set -- homomorphism of structures
    H-is-hprop : (x y : pcat.A₀ X) (α : P x) (β : P y) (f : pcat.A₁ X x y) → is-hprop (H x y α β f)
    H-id : (x : pcat.A₀ X) (α : P x) → H x x α α (pcat.id X x)
    H-comp : (x y z : pcat.A₀ X) (α : P x) (β : P y) (γ : P z)  (f : pcat.A₁ X y z) → (g : pcat.A₁ X x y) →
      (H y z β γ f) → (H x y α β g) → (H x z α γ (pcat._∘_ X x y z f g))
    --leq : (x : pcat.A₀ X) → (α β : P x) → Set
    --leq x α β = H (pcat.id X x)

H-lemma : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → (g : pcat.A₁ X y z) → (f == g) → str.H S y z β γ  f → str.H S y z β γ g
H-lemma X S f .f idp = λ z → z

-- left unit for a structure homomorphism
H-ul : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S y z β γ f → str.H S y z β γ (pcat._∘_ X y z z (pcat.id X z) f)
H-ul = λ X S {y} {z} {β} {γ} f → str.H-comp S y z z β γ γ (pcat.id X z) f (str.H-id S z γ)

H-ul-inv : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S y z β γ (pcat._∘_ X y z z (pcat.id X z ) f) → str.H S y z β γ f
H-ul-inv X S {y} {z} {β} {γ} f w = H-lemma X S (pcat._∘_ X y z z (pcat.id X z) f) f (! (pcat.ul X y z f)) w

-- right unit for a structure homomorphism
H-ur : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S y z β γ f → str.H S y z β γ (pcat._∘_ X y y z f (pcat.id X y))
H-ur = λ X S {y} {z} {β} {γ} f z₁ → str.H-comp S y y z β β γ f (pcat.id X y) z₁ (str.H-id S y β)

--H-ur' : (X : pcat) → (S : str X) {y z : pcat.A₀ X}{β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) →
--          (str.H S f  == str.H S (pcat._∘_ X f (pcat.id X)))
--H-ur' X S {y} {z} {β} {γ} f = ap (λ g → str.H S g) (pcat.ur X f)

--H-ur' : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → (w : str.H S f) →
--      transport (λ v → str.H S v) (pcat.ur X f) w == str.H-comp S f (pcat.id X) w (str.H-id S)
--H-ur' X S {y} {z} {β} {γ} f w = ap {pcat.A₁ X y z} {?} ? {pcat._∘_ X f (pcat.id X)} {f} (! (pcat.ur X f))

H-ur-inv : (X : pcat) → (S : str X) {y z : pcat.A₀ X} {β : str.P S y} {γ : str.P S z} → (f : pcat.A₁ X y z) → str.H S y z β γ (pcat._∘_ X y y z f (pcat.id X y)) → str.H S y z β γ f
H-ur-inv X S {y} {z} {β} {γ} f w = H-lemma X S (pcat._∘_ X y y z f (pcat.id X y)) f (! (pcat.ur X y z  f)) w

-- Order on the interpretation of an object
leq : (X : pcat) → (S : str X) → (x : pcat.A₀ X) → (α β : str.P S x) → Set
leq X S x α β = str.H S x x α β (pcat.id X x)

-- Standard notion of structure
record stdstr (X : pcat) : Set₁ where
  field
    S : str X
    spleq : (x : pcat.A₀ X) → (α β : str.P S x) → (leq X S x α β ) → (leq X S x β α) → (α == β)

postulate --we tried proving these and failed miserably

  leo-r : (X : pcat) → (S : str X) → {x y : pcat.A₀ X} (f : pcat.A₁ X x y) → (α : str.P S x) → (β : str.P S y) → (snd : str.H S x y α β f) →
    transport (λ v → str.H S x y α β v) (pcat.ur X x y f) snd == str.H-comp S x x y α α β f (pcat.id X x) snd (str.H-id S x α)
--leo-r X S {x} {y}  f α β snd = ap (λ z → str.H-comp S x x y α α β ? (pcat.id X x) ? (str.H-id S x α)) (Σ-stuff.decode (f , snd) (f , snd) (Σ-stuff.Σ-eq-in idp idp))

  leo-l : (X : pcat) → (S : str X) → {x y : pcat.A₀ X} (f : pcat.A₁ X x y) → (α : str.P S x) → (β : str.P S y) → (snd : str.H S x y α β f)→
    transport (λ v → str.H S x y α β v) (pcat.ul X x y f) snd == str.H-comp S x y y α β β (pcat.id X y) f (str.H-id S y β) snd
--leo-l X S f snd = ap (λ z → str.H-comp S (pcat.id X) f (str.H-id S) snd) (Σ-stuff.decode (f , snd) (f , snd) (Σ-stuff.Σ-eq-in idp idp))

  leo-α : (X : pcat) → (S : str X) → {x y z w : pcat.A₀ X} (f : pcat.A₁ X x y) → (g : pcat.A₁ X y z) → (h : pcat.A₁ X z w) → (α : str.P S x) → (β : str.P S y) → (γ : str.P S z) → (δ : str.P S w) → (H-f : str.H S x y α β f) → (H-g : str.H S y z β γ g) → (H-h : str.H S z w γ δ h) →
    transport (λ v → str.H S x w α δ v) (pcat.α X x y z w f g h) (str.H-comp S x z w α γ δ h (pcat._∘_ X x y z g f) H-h (str.H-comp S x y z α β γ g f H-g H-f)) == (str.H-comp S x y w α β δ (pcat._∘_ X y z w h g) f (str.H-comp S y z w β γ δ h g H-h H-g) H-f)
--leo-α X S {x} {y} {z} {w} f  g h α β γ δ H-f H-g H-h = ap (λ a → str.H-comp S x y w α β δ (pcat._∘_ X y z w h g) f (str.H-comp S y z w β γ δ h g H-h H-g) H-f) idp

-- Precategory of structures
pcatstr : (X : pcat) → (S : str X) → pcat
pcatstr X S =
  record { A₀ = Σ  (pcat.A₀ X) (str.P S) ;
    A₁ = λ {(x , α) (y , β) → Σ (pcat.A₁ X x y) λ f → str.H S x y α β f} ;
    A₁-is-hset =    λ { a b x .x idp idp → idp};
    id  = λ {x  → (pcat.id X (Σ.fst x) , str.H-id S (Σ.fst x) (Σ.snd x))} ;
    _∘_ = λ {x y z (fst , snd) (fst₁ , snd₁) → (pcat._∘_ X (Σ.fst x) (Σ.fst y) (Σ.fst z) fst fst₁) , str.H-comp S (Σ.fst x) (Σ.fst y) (Σ.fst z) (Σ.snd x) (Σ.snd y) (Σ.snd z) fst fst₁ snd snd₁} ;
    ur = λ {x y (f , snd) → Σ-stuff.decode (f , snd) ((pcat._∘_ X (Σ.fst x) (Σ.fst x) (Σ.fst y) f (pcat.id X (Σ.fst x))) , str.H-comp S (Σ.fst x) (Σ.fst x) (Σ.fst y) (Σ.snd x) (Σ.snd x) (Σ.snd y) f (pcat.id X (Σ.fst x)) snd (str.H-id S (Σ.fst x) (Σ.snd x)))
        (Σ-stuff.Σ-eq-in (pcat.ur X (Σ.fst x) (Σ.fst y) f) (leo-r X S f (Σ.snd x) (Σ.snd y) snd) )} ;
    ul = λ {x y (f , snd) → Σ-stuff.decode (f , snd) ((pcat._∘_ X (Σ.fst x) (Σ.fst y) (Σ.fst y) (pcat.id X (Σ.fst y)) f) , str.H-comp S (Σ.fst x) (Σ.fst y) (Σ.fst y) (Σ.snd x) (Σ.snd y) (Σ.snd y) (pcat.id X (Σ.fst y)) f (str.H-id S (Σ.fst y) (Σ.snd y)) snd)
        (Σ-stuff.Σ-eq-in (pcat.ul X (Σ.fst x) (Σ.fst y) f) (leo-l X S f (Σ.snd x) (Σ.snd y) snd) )} ;
    α = λ {x y z w (f , H-f) (g , H-g) (h , H-h) → Σ-stuff.decode ((pcat._∘_ X (Σ.fst x) (Σ.fst z) (Σ.fst w) h (pcat._∘_ X (Σ.fst x) (Σ.fst y) (Σ.fst z) g f))
      , str.H-comp S (Σ.fst x) (Σ.fst z) (Σ.fst w) (Σ.snd x) (Σ.snd z) (Σ.snd w)  h (pcat._∘_ X (Σ.fst x) (Σ.fst y) (Σ.fst z) g f) H-h (str.H-comp S (Σ.fst x) (Σ.fst y) (Σ.fst z) (Σ.snd x) (Σ.snd y) (Σ.snd z) g f H-g H-f)) ((pcat._∘_ X (Σ.fst x) (Σ.fst y) (Σ.fst w) (pcat._∘_ X (Σ.fst y) (Σ.fst z) (Σ.fst w) h g) f) ,
      (str.H-comp S (Σ.fst x) (Σ.fst y) (Σ.fst w) (Σ.snd x) (Σ.snd y) (Σ.snd w) (pcat._∘_ X (Σ.fst y) (Σ.fst z) (Σ.fst w) h g) f (str.H-comp S (Σ.fst y) (Σ.fst z) (Σ.fst w) (Σ.snd y) (Σ.snd z) (Σ.snd w) h g H-h H-g) H-f)) (Σ-stuff.Σ-eq-in
        (pcat.α X (Σ.fst x) (Σ.fst y) (Σ.fst z) (Σ.fst w) f g h) (leo-α X S  f g h (Σ.snd x) (Σ.snd y) (Σ.snd z) (Σ.snd w) H-f H-g H-h)) }}


--transport-lemma : (X : cat) → (S : stdstr  (cat.precat X)) → (a b : pcat.A₀ (cat.precat X)) → (p : a == b) → (α : str.P (stdstr.S S) a) → (β : str.P (stdstr.S S) b) →
 -- (transport (str.P (stdstr.S S)) p α) == β
--transport-lemma X S a .a idp α β  = stdstr.spleq S a α β {!!} {!!}


iwannadie1 : ( X : cat) → ( S : str (cat.precat X)) → (a b : pcat.A₀ (cat.precat X)) → (α : str.P S a) → (β : str.P S b) → (f : pcat.A₁ (cat.precat X) a b) → (w : str.H S a b α β f) → (i : iso (cat.precat X) f )
  → str.H S a b α β (Σ.fst (id-to-iso (cat.precat X) (is-hae.g (cat.wit-hae X) (f , i) )))
iwannadie1 X S a b α β f w i = H-lemma (cat.precat X) S f ( (Σ.fst (id-to-iso (cat.precat X) (is-hae.g (cat.wit-hae X) (f , i) )))) {! !} {! !}
--(Σ.fst (id-to-iso (cat.precat X) (is-hae.g (cat.wit-hae X) (f , i) )))

--leo-thm : (X : cat) → (S : stdstr (cat.precat X)) →
 --   {a b : Σ  (pcat.A₀ (cat.precat X)) (str.P (stdstr.S S))} → (p : a == b) → (α : str.P (stdstr.S S) (Σ.fst a)) → (β : str.P (stdstr.S S) (Σ.fst b)) →
  --  (transport (str.P (stdstr.S S)) (Σ-stuff.Σ-eq.fst-eq (Σ-stuff.encode a b p)) α) == β
--leo-thm X S {a} {b} idp  α β = stdstr.spleq S (Σ.fst a) α β {!!} {!!}

--iwannadie2 : ( X : cat) → (S : str (cat.precat X)) → (x y : pcat.A₀  (pcatstr (cat.precat X) S))  → (f : pcat.A₁ (pcatstr (cat.precat X) S) x y) → (i : iso (pcatstr (cat.precat X)  S) f) → (p : x == y)
--  → transport (str.P (S)) (iso-to-id X (Σ.fst f) (record{ g = Σ.fst (iso.g i); τ = ap Σ.fst (iso.τ i)  ; ε = ap Σ.fst (iso.ε i)})) (Σ.snd x) == (transport (str.P (S)) (Σ-stuff.Σ-eq.fst-eq (Σ-stuff.encode x y p)) (Σ.snd x))
--iwannadie2 X S x .x f i idp = {!!}

iwannadie3 : ( X : cat) → (S : stdstr (cat.precat X)) → (x y : pcat.A₀  (pcatstr (cat.precat X) (stdstr.S S)))  → (f : pcat.A₁ (pcatstr (cat.precat X) (stdstr.S S)) x y) → (i : iso (pcatstr (cat.precat X)  (stdstr.S S)) f) → (p : Σ.fst x == Σ.fst y)
  → transport (str.P (stdstr.S S)) (iso-to-id X (Σ.fst f , (record{ g = Σ.fst (iso.g i); τ = ap Σ.fst (iso.τ i)  ; ε = ap Σ.fst (iso.ε i)}))) (Σ.snd x) == Σ.snd y
iwannadie3 X S (.(Σ.fst y) , snd) y f i idp = stdstr.spleq S (Σ.fst y) (transport (str.P (stdstr.S S)) (iso-to-id X ((Σ.fst f) , (record{ g = Σ.fst (iso.g i); τ = ap Σ.fst (iso.τ i)  ; ε = ap Σ.fst (iso.ε i)}))) snd) (Σ.snd y)
  (H-lemma (cat.precat X) (stdstr.S S) (pcat._∘_ (cat.precat X) (Σ.fst y) (Σ.fst y) {!  !} {!   !} {!   !}) {!   !} {!   !} {!   !}) (H-lemma (cat.precat X) (stdstr.S S) {!  !} {!  !} {!  !} {!  !})

-- The structure identity principle

str-id-ppl : (X : cat) → (S : stdstr (cat.precat X)) → (x y : pcat.A₀ (pcatstr (cat.precat X) (stdstr.S S))) → (f : pcat.A₁ (pcatstr (cat.precat X) (stdstr.S S)) x y) → (i : iso (pcatstr (cat.precat X) (stdstr.S S)) f) → x == y
str-id-ppl X S x y f i = Σ-stuff.decode x y (Σ-stuff.Σ-eq-in (iso-to-id X ((Σ.fst f) , (record { g = Σ.fst (iso.g i) ; τ = ap (λ x → Σ.fst x) (iso.τ i) ; ε = ap (λ x → Σ.fst x) (iso.ε i) })))
  ( iwannadie3 X S x y f i ((iso-to-id X ((Σ.fst f) , (record { g = Σ.fst (iso.g i) ; τ = ap (λ x → Σ.fst x) (iso.τ i) ; ε = ap (λ x → Σ.fst x) (iso.ε i) })))) ))

record magma (A : Set) : Set where
  field
    _*_ : A → A → A

record monoid (A : Set) : Set where
  field
    _*_ : A → A → A
    m_unit : A
    α : (a b c : A) → ((a * b) * c) == (a * (b * c))
    ur : (a : A) → (a == (a * m_unit))
    ul : (a : A) → (a == (m_unit * a))


record group (A : Set) : Set where
  field
    _*_ : A → A → A
    g_unit : A
    α : (a b c : A) → ((a * b) * c) == (a * (b * c))
    ur : (a : A) → (a == (a * g_unit))
    ul : (a : A) → (a == (g_unit * a))
