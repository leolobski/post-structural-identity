{-# OPTIONS --without-K --no-eta-equality #-}

open import Equality

module 3DependentTypes2 where

{- We are going to carry out the encode decode method for Σ types. Throughout this
   argument we want to fix a type A and a dependent type B over A. We will do this
   using a module. Any definition inside the module is free to refer to the module
   arguments A and B without listing them as arguments.
-}
module Σ-encode-decode {A : Set} {B : A → Set} where

  {- The first step is to define a relation on Σ A B that should be equivalent
     to the identity type. For this we will use the record type Σ-eq below.
  -}
  record Σ-eq (ab ab' : Σ A B) : Set where
    constructor Σ-eq-in
    field
      fst-eq : Σ.fst ab == Σ.fst ab'
      snd-eq : (ap {A} {B} fst-eq (Σ.snd ab)) == Σ.snd ab'
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
