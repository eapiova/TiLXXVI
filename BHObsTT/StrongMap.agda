{-# OPTIONS --cubical --safe #-}

module BHObsTT.StrongMap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (Σ; fst; snd; _,_)
open import HObsTT.Universe using (U; El)
open import HObsTT.Eq using (Eq; eqToPath; pathToEq)
open import HObsTT.CoEq using (CoEq)
open import HObsTT.AUC using (StronglyExtensional)

StrongMap : U → U → Type₀
StrongMap A B = Σ (El A → El B) (StronglyExtensional A B)

mapFun : {A B : U} → StrongMap A B → El A → El B
mapFun = fst

mapCoap : {A B : U} (h : StrongMap A B) →
  StronglyExtensional A B (mapFun h)
mapCoap = snd

idStrong : (A : U) → StrongMap A A
idStrong A = (λ x → x) , λ x x' d → d

compStrong :
  {A B C : U} → StrongMap B C → StrongMap A B → StrongMap A C
compStrong g f =
  (λ x → mapFun g (mapFun f x)) ,
  λ x x' d →
    mapCoap f x x' (mapCoap g (mapFun f x) (mapFun f x') d)

-- Weak maps respect equality for free (mapEq); strong maps additionally
-- reflect apartness. The gap between the two is the subject of the
-- calibration results in HObsTT.
mapEq : {A B : U} (f : El A → El B) {x x' : El A} →
  Eq A x x' → Eq B (f x) (f x')
mapEq {A = A} {B = B} f {x = x} {x' = x'} e =
  pathToEq B (f x) (f x') (cong f (eqToPath A x x' e))

-- This is the contrapositive of equality preservation by a weak map.
mapNegEq : {A B : U} (f : El A → El B) {x x' : El A} →
  (Eq B (f x) (f x') → ⊥) → Eq A x x' → ⊥
mapNegEq f notEq e = notEq (mapEq f e)
