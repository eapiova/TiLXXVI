{-# OPTIONS --cubical --safe #-}

module BHObsTT.StrongConnectives where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (inl to inl'; inr to inr')
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as Empty using (⊥)
open import HObsTT.Universe using (U; El)
open import HObsTT.Eq using (eqRefl)
open import HObsTT.CoEq using (CoEq)
open import HObsTT.EfQ using (EfQ-CoEq)
open import HObsTT.Polarization using
  ( leftB
  ; rightB
  ; Tensor
  ; With
  ; Plus
  ; tensorDual→
  ; tensorDual←
  ; withDual→
  ; withDual←
  ; plusDualInl→
  ; plusDualInl←
  ; plusDualInr→
  ; plusDualInr←
  ; plusDualMixed
  )
open import BHObsTT.StrongMap using
  ( StrongMap
  ; mapFun
  ; mapCoap
  ; compStrong
  ; mapEq
  )

proj₁With : (A B : U) → StrongMap (With A B) A
proj₁With A B =
  (λ F → F leftB) ,
  λ F G d → withDual← A B F G (inl' d)

proj₂With : (A B : U) → StrongMap (With A B) B
proj₂With A B =
  (λ F → F rightB) ,
  λ F G d → withDual← A B F G (inr' d)

private
  withPairFun :
    {C A B : U} →
    StrongMap C A → StrongMap C B → El C → El (With A B)
  withPairFun f g c (zero , _)          = mapFun f c
  withPairFun f g c (suc zero , _)      = mapFun g c
  withPairFun f g c (suc (suc _) , ())

  withPairCoap :
    {C A B : U} (f : StrongMap C A) (g : StrongMap C B) →
    (c c' : El C) →
    CoEq (With A B) (withPairFun f g c) (withPairFun f g c') →
    CoEq C c c'
  withPairCoap {A = A} {B = B} f g c c' d
    with withDual→ A B (withPairFun f g c) (withPairFun f g c') d
  ... | inl' dA = mapCoap f c c' dA
  ... | inr' dB = mapCoap g c c' dB

pairWith :
  {C A B : U} → StrongMap C A → StrongMap C B → StrongMap C (With A B)
pairWith f g = withPairFun f g , withPairCoap f g

pairWithβ₁ :
  {C A B : U} (f : StrongMap C A) (g : StrongMap C B) →
  mapFun (compStrong (proj₁With A B) (pairWith f g)) ≡ mapFun f
pairWithβ₁ f g = funExt λ c → refl

-- The universal property is stated on function parts only; uniqueness of
-- the co-ap component is NOT available because CoEq is proof-relevant.
-- This is an exact-hypothesis boundary.

inj₁Plus : (A B : U) → StrongMap A (Plus A B)
inj₁Plus A B =
  (λ a → leftB , a) ,
  λ a a' d → plusDualInl→ A B a a' d

inj₂Plus : (A B : U) → StrongMap B (Plus A B)
inj₂Plus A B =
  (λ b → rightB , b) ,
  λ b b' d → plusDualInr→ A B b b' d

private
  plusCopairFun :
    {A B C : U} →
    StrongMap A C → StrongMap B C → El (Plus A B) → El C
  plusCopairFun f g ((zero , _) , a)          = mapFun f a
  plusCopairFun f g ((suc zero , _) , b)      = mapFun g b
  plusCopairFun f g ((suc (suc _) , ()) , _)

  plusCopairCoap :
    {A B C : U} (f : StrongMap A C) (g : StrongMap B C) →
    (x x' : El (Plus A B)) →
    CoEq C (plusCopairFun f g x) (plusCopairFun f g x') →
    CoEq (Plus A B) x x'
  plusCopairCoap {A = A} {B = B} f g
    ((zero , _) , a) ((zero , _) , a') d =
      plusDualInl← A B a a' (mapCoap f a a' d)
  plusCopairCoap {A = A} {B = B} f g
    ((suc zero , _) , b) ((suc zero , _) , b') d =
      plusDualInr← A B b b' (mapCoap g b b' d)
  plusCopairCoap {A = A} {B = B} f g
    ((zero , _) , a) ((suc zero , _) , b) d =
      plusDualMixed A B a b
  plusCopairCoap {A = A} {B = B} f g
    ((suc zero , _) , b) ((zero , _) , a) d =
      λ e → EfQ-CoEq A _ a (e .fst)
  plusCopairCoap {A = A} {B = B} f g
    ((suc (suc _) , ()) , _) _ _
  plusCopairCoap {A = A} {B = B} f g
    _ ((suc (suc _) , ()) , _) _

copairPlus :
  {A B C : U} → StrongMap A C → StrongMap B C → StrongMap (Plus A B) C
copairPlus f g = plusCopairFun f g , plusCopairCoap f g

tensorMap :
  {A A' B B' : U} →
  StrongMap A A' → StrongMap B B' →
  StrongMap (Tensor A B) (Tensor A' B')
tensorMap {A = A} {A' = A'} {B = B} {B' = B'} f g =
  (λ (a , b) → mapFun f a , mapFun g b) ,
  λ (a , b) (a' , b') d →
    tensorDual← A B λ e →
      mapCoap g b b'
        (tensorDual→ A' B' d (mapEq (mapFun f) e))

curryPartial :
  {A B C : U} →
  StrongMap (Tensor A B) C → (a : El A) → StrongMap B C
curryPartial {A = A} {B = B} h a =
  (λ b → mapFun h (a , b)) ,
  λ b b' d →
    tensorDual→ A B
      (mapCoap h (a , b) (a , b') d)
      (eqRefl A a)

-- NOTE: the co-ap of a ↦ curryPartial h a is not statable: StrongMap B C is
-- not the decoding of any code, so no CoEq is defined on it. This is
-- precisely the representability question for a strong Π; see the roadmap.
