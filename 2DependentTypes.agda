{-# OPTIONS --without-K #-}

{- Some of the definitions from last time have been copied to the two files Naturals.agda
   and Bool.agda. The next two lines "import" the definitions into this file. This allows
   us to use the definitions in this file without writing them out again. For this to work
   you need to download the two files from my website and put them in the same directory
   as this file.
-}
open import Naturals
open import Bool

module 2DependentTypes where

{- Recall from last time that we can define equality (or identity, or path) types as
   an indexed inductive definition below. To prove something about all proofs of equality
   we only have prove it about reflexivity.
-}
data _==_ {X : Set} (x : X) : X → Set where
  idp : x == x -- idp is short for "identity path". The HoTT book says refl instead.



{- The product of two types. This corresponds to conjunction (and) under
   propositions-as-types.
-}
data _⊓_ (X Y : Set) : Set where
  _,_ : X → Y → (X ⊓ Y) -- remember to not put spaces between _ and ,


{- The first and second projects of the product -}
first-proj : {X Y : Set} → (X ⊓ Y) → X
first-proj (x , y) = x -- remember to put a space beween x and ,

second-proj : {X Y : Set} → (X ⊓ Y) → Y
second-proj (x , y) = y

record Pair (X Y : Set) : Set where
  constructor pair
  field
    first : X
    second : Y


{- Exercise 1: Show that Pair X Y is equivalent to Pair Y X by
               filling the two goals below -}
{- Hint: Pattern matching can be done for record types with constructors -}
swap : {X Y : Set} → (Pair X Y) → (Pair Y X)
swap (pair x y) = pair y x

swap-inv : {X Y : Set} → (p : Pair X Y) → (swap (swap p) == p)
swap-inv (pair first second) = idp


{- The diagonal map using the record keyword -}
diag : {X : Set} → X → Pair X X
diag x = record { first = x ; second = x }

{- An alternative definition of the diagonal map
   using the pair constructor -}
diag' : {X : Set} → X → Pair X X
diag' x = pair x x

{- Last time we defined, but didn't cover in detail disjoint sum (also known as
   coproduct). Here it is again. ⊔ is written \sqcup. This corresponds to disjunction
   (or) under propositions-as-types.
-}
data _⊔_ (X Y : Set) : Set where
  inl : (x : X) → X ⊔ Y
  inr : (y : Y) → X ⊔ Y

{- The recursion principle for coproducts -}
⊔-rec : {X Y Z : Set} → (X → Z) → (Y → Z) → (X ⊔ Y) → Z
⊔-rec f g (inl x) = f x
⊔-rec f g (inr y) = g y

infix 20 _⊔_


{- Exercise 2: Construct a term of the type below.
   Via propositions as types it can either be viewed as functoriality of
   ⊔ or as the logical principle constructive dilemma.
-}
constructive-dilemma : {A B C D : Set} → (A → C) → (B → D) → (A ⊔ B) → (C ⊔ D)
constructive-dilemma f g (inl a) =  inl (f a)
constructive-dilemma f g (inr b) = inr (g b)


{- Function types -}
{- Usually we just use X → Y directly, so there is never any need to
   use this function!
-}
functions : (X Y : Set) → Set
functions X Y = X → Y

{- For any type X we define the identity function on X. -}
{- We can either define it using pattern matching like this -}
idf : (X : Set) → X → X
idf X x = x

{- Alternatively we could have used a lambda expression like this -}
idf' : (X : Set) → X → X
idf' X = λ x → x

{- Using C-c C-n you can see that idf and idf' have the same normal forms
   and so they are definitionally equal. -}

{- Exercise 3: Define the composition of two funtions f and g below. -}
compose : {X Y Z : Set} (f : X → Y) (g : Y → Z) → (X → Z)
compose f g x = g (f x)

{- Composition is often written using ∘ (\o) as below -}
_∘_ : {X Y Z : Set} (g : Y → Z) (f : X → Y) → (X → Z)
g ∘ f = compose f g


{- Exercise 4: Given types X and Y and an element y of Y, define the
               function constantly equal to y below.
               Try doing this using a λ term and also using pattern matching
-}
cst : {X Y : Set} (y : Y) → (X → Y)
cst y = λ x → y

cst' : {X Y : Set} (y : Y) → (X → Y)
cst' y x = y

{- alternative definition of times, using iter and a lambda term -}
times' : ℕ → ℕ → ℕ
times' n m = iter ℕ 0 (λ x → x + n) m

{- Exercise 5: Give another proof of constructive dilemma using ⊔-rec -}
constructive-dilemma' : {A B C D : Set} → (A → C) → (B → D) → (A ⊔ B) → (C ⊔ D)
constructive-dilemma' f g x = ⊔-rec (compose f inl) (compose g inr) x


{- Recall from last time that we can define True and False as the types ⊤ and ⊥ below. -}
data ⊥ : Set where

data ⊤ : Set where
  unit : ⊤

{- Also recall that we can define the function exfalso from ⊥ into any type -}
exfalso : {X : Set} → ⊥ → X
exfalso ()


{- We define negation below. This says that X is false (viewed as a proposition)
   or empty (viewed as a set).
-}
¬ : Set → Set
¬ X = X → ⊥

{- Exercise 6: From X → Y, prove its contraposition -}
modus-tollens : {X Y : Set} → (X → Y) → (¬ Y → ¬ X)
modus-tollens f g =  g ∘ f

modus-tollens' : {X Y : Set} → (X → Y) → (¬ Y → ¬ X)
modus-tollens' f g = (λ x → (g ∘ f) x)

modus-tollens'' : {X Y : Set} → (X → Y) → (¬ Y → ¬ X)
modus-tollens'' f = (λ g → g ∘ f)

{- Exercise 7: If p or q is true and q is false, then p is true. This is known
   as the disjunction syllogism.
-}
disj-syllogism : {P Q : Set} → (P ⊔ Q) → ¬ Q → P
disj-syllogism (inl p) y = p
disj-syllogism (inr q) y = exfalso (y q)

--HOMEWORK: up to ex 13

{- We use the following special notation for not equal
   (≠ is written using \neq)
-}
_≠_ : {X : Set} (x y : X) → Set
x ≠ y = ¬ (x == y)

infix 30 _≠_


{- Showing that true is not equal to false, is another example where we
   can use absurd pattern matching. (Exercise: Think about why this is!)
-}
true-≠-false : true ≠ false
true-≠-false ()


{- The definition of dependent products, also known as Π-types (Pi-types) -}
{- Just like with functions, we hardly ever need to use the definition
   Π below, because we can always just write (x : X) → Y x directly
-}
Π : (X : Set) (Y : X → Set) → Set
Π X Y = (x : X) → Y x

{- We construct a function from x == y to y == x by pattern matching.
   Note that we have written .x for the second argument. These is referred to
   as a "dot pattern" or "inaccessible pattern." It signifies that the second
   argument is forced to be equal to x by the other arguments, in this case
   because the third argument is idp, it is forced to be equal to the second
   argument.
 -}
symmetric : {X : Set} (x y : X) → (x == y) → (y == x)
symmetric x .x idp = idp

{- We often use the following notation for symmetric.
   We think of this as reversing the direction of a path.
   Note that we have now made x and y into implicit arguments, when
   they weren't implicit for the function symmetric. This
   is often more useful in practice.
-}
! : {X : Set} {x y : X} → (x == y) → (y == x)
! {X} {x} {y} p = symmetric x y p


{- The induction principle for equality is the function J defined
   below. This is called ind= in the HoTT book. -}
J : {X : Set} (C : (x : X) → (y : X) → (p : x == y) → Set)
    (c : (x : X) → (C x x idp)) → (x y : X) → (p : x == y) → C x y p
J C c x .x idp = c x

-- NB: In practice we can usually use pattern matching directly instead of J

{- Exercise 8: Show symmetric can be derived using J. Some of the values
   have been filled in already.
-}

C : {X : Set} (x y : X) → (x == y) → Set
C x y p = (y == x)

c : {X : Set} (x : X) → (C x x idp)
c x = idp

symmetric' : {X : Set} (x y : X) → (x == y) → (y == x)
symmetric' x y p = J C c x y p


{- Exercise 9: prove that if x == y and y == z, then x == z,
   by constructing a function of the type below by pattern matching -}
transitive : {X : Set} {x y z : X} → (x == y) → (y == z) → (x == z)
transitive idp idp = idp

{- Instead of using trans directly, we usually use the mixfix
   notation ∙ (written \. )
   Topologically we think of p ∙ q as concatenating two paths p and q.
-}
_∙_ : {X : Set} {x y z : X} → (x == y) → (y == z) → (x == z)
p ∙ q = transitive p q

infix 50 _∙_

{- Exercise 10: Define transport below. This takes a dependent type Y : X → Set
   and a path p from x to y in X, and gives us a map from Y x to Y y
-}
transport : {X : Set} {Y : X → Set} {x y : X} (p : x == y) → (Y x) → (Y y)
transport idp y = y


{- Action on paths is an important function in type theory -}
ap : {X Y : Set} (f : X → Y) {x y : X} → (x == y) → (f x == f y)
ap f idp = idp

{- For example, in the exercise below, you might find ap useful -}

{- If two terms are definitionally equal they are trivially
   propositionally equal. Here is an example. -}
move-succ1 : (n m : ℕ) → (n + (succ m) == succ (n + m))
move-succ1 n m = idp
  -- n + (succ m) and succ (n + m) are definitionally equal so we can use idp


{- succ n + m and succ (n + m) are not definitionally equal - check this by
   navigating to the goal, entering
   idp as proof and observing that it does not typecheck. -}
{- Exercise 11: prove that they are propositionally equal by filling the goal -}
move-succ2 : (n m : ℕ) → ((succ n) + m == succ (n + m))
move-succ2 n zero = idp
move-succ2 n (succ m) = ap succ (move-succ2 n m)



{- Similarly, if two functions f and g are equal, then so are f x
   and g x for all x
-}
app= : {X Y : Set} (f g : X → Y) (p : f == g) (x : X) → (f x == g x)
app= f .f idp x = idp

{- Exercise 12: derive app= as a special case of ap -}
app=' : {X Y : Set} (f g : X → Y) (p : f == g) (x : X) → (f x == g x)
app=' f .f idp x = ap f idp


{- Note that any type has an identity type, even identity types themselves. -}

{- Exercise 13: show that the concatenation of the two paths ! p followed by p
   is equal to the path idp by filling the hole below.
-}
!-inv-l : {X : Set} {x y : X} (p : x == y) → (((! p) ∙ p) == idp )
!-inv-l idp = idp

{- As a special case of !-inv-l, we can take y to be the variable x
   giving the function below. Observe that there is
   no obvious way to use pattern matching or J directly to prove this.
-}
inv1 : {X : Set} {x : X} (p : x == x) → (((! p) ∙ p) == idp)
inv1 p = !-inv-l p


{- Recall from last time the function is-true from Bool to Set. -}
{- For a boolean, b, the type 'is-true b' contains an element if and only if b is true -}
is-true : Bool → Set
is-true true = ⊤
is-true false = ⊥

{- Last time we saw the function istrue : Bool → Set
   Show we can define maps back and forth between
   p == true and istrue p in the goals below
-}
=true-istrue : (b : Bool) → (b == true) → (is-true b)
=true-istrue true idp = unit
=true-istrue false ()

istrue-=true : (b : Bool) → (is-true b) → (b == true)
istrue-=true true unit = idp
istrue-=true false ()


{- The definition of dependent pairs/Σ-types -}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

{- Exercise 14: Give an alternative definition, Sigma of Σ using a data
   type instead of record, and show how to define a map from Σ A B to
   Sigma A B and a map back from Sigma A B to Σ A B -}

{- data _⊔_ (X Y : Set) : Set where
  inl : (x : X) → X ⊔ Y
  inr : (y : Y) → X ⊔ Y -}

data Sigma (A : Set) (B : A → Set) : Set where
  incl : (a : A) → (B a → Sigma A B)

Σ-to-Sigma : (A : Set) (B : A → Set) → (Σ A B) → Sigma A B
Σ-to-Sigma A B f = incl (Σ.fst f) (Σ.snd f)

Sigma-to-Σ : (A : Set) (B : A → Set) → (Sigma A B) → Σ A B
Sigma-to-Σ A B (incl a b) = (a , b)

{- We will show that Pair can be defined using Σ as follows -}
Pair' : (X Y : Set) → Set
Pair' X Y = Σ X (λ _ → Y)

{- Exercise 15: Construct a function from Pair X Y to Pair' X Y -}
Pair-to-Pair' : {X Y : Set} → (Pair X Y) → (Pair' X Y)
Pair-to-Pair' (pair x y) = (x , y)

{- Exercise 16: Construct a function from Pair' X Y to Pair X Y -}
Pair'-to-Pair : {X Y : Set} → (Pair' X Y) → (Pair X Y)
Pair'-to-Pair (fst , snd) = pair fst snd

{- Exercise 17: Show that the two functions above are mutually inverse
   (fill both of the two holes below).
-}
Pair-inverse1 : (X Y : Set) (xy : Pair' X Y) → (Pair-to-Pair' (Pair'-to-Pair xy) == xy)
Pair-inverse1 X Y xy =  idp

Pair-inverse2 : (X Y : Set) (xy : Pair X Y) → (Pair'-to-Pair (Pair-to-Pair' xy) == xy)
Pair-inverse2 X Y xy =   idp

{- Homework -}

{- 1. Fill the goal below. This is an important construction known as whiskering. -}
whisker-l : {X : Set} {x y z : X} (p q : x == y) (α : p == q) (r : y == z) → (p ∙ r == q ∙ r)
whisker-l {X} {x} {.x} {.x} idp .idp idp idp = idp

{- 2. -}
{- This is an example of the encode-decode argument.
   We will define a relation ∼ on the natural numbers. We will then
   afterwards show that it is "the same" as ==. This helps us to prove
   facts about equality on ℕ that would otherwise be difficult.
-}
_∼_ : (n m : ℕ) → Set
zero ∼ zero = ⊤
zero ∼ succ m = ⊥
succ n ∼ zero = ⊥
succ n ∼ succ m = n ∼ m

{- 2.(a) Prove that ∼ is reflexive (fill the goal below) -}
∼-refl : (n : ℕ) → (n ∼ n)
∼-refl zero = unit
∼-refl (succ n) = ∼-refl n

{- We can convert from equality to the new relation ∼.
   This is called encoding.
   2.(b) Construct the encoding function below.
-}
encode : (n m : ℕ) → (n == m) → (n ∼ m)
encode n .n idp = ∼-refl n

{- We can also convert back the other way.
   This is called decoding.
   2.(c) Construct the decoding function below.
-}
decode : (n m : ℕ) → (n ∼ m) → (n == m)
decode zero zero unit = idp
decode (succ n) zero ()
decode zero (succ m) ()
decode (succ n) (succ m) x = ap succ (decode n m x)

{- 2.(d) Prove that for any two numbers n and m,
   n ∼ n is either true or false (the goal below).
-}
∼-dec : (n m : ℕ) → ((n ∼ m) ⊔ ¬ (n ∼ m))
∼-dec zero zero = inl unit
∼-dec zero (succ m) = inr λ z → z
∼-dec (succ n) zero = inr λ z → z
∼-dec (succ n) (succ m) = ∼-dec n m

{- 2.(e) Use the above parts to show that equality is
   decidable for ℕ (the goal below).
 -}
ℕ-=-dec : (n m : ℕ) → ((n == m) ⊔ ¬ (n == m))
ℕ-=-dec n m =  constructive-dilemma (decode n m) (modus-tollens (encode n m)) (∼-dec n m)
