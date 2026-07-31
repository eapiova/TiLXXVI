{-# OPTIONS --cubical --safe #-}

module HObsTT.Involutivity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq

CoCoEqℕ : ℕ → ℕ → Type₀
CoCoEqℕ zero zero       = Unit
CoCoEqℕ zero (suc m)    = ⊥
CoCoEqℕ (suc n) zero    = ⊥
CoCoEqℕ (suc n) (suc m) = CoCoEqℕ n m

cocoToEqℕ : (n m : ℕ) → CoCoEqℕ n m → Eq nat' n m
cocoToEqℕ zero zero _ = tt
cocoToEqℕ zero (suc m) ()
cocoToEqℕ (suc n) zero ()
cocoToEqℕ (suc n) (suc m) cc = cocoToEqℕ n m cc

eqToCoCoEqℕ : (n m : ℕ) → Eq nat' n m → CoCoEqℕ n m
eqToCoCoEqℕ zero zero _ = tt
eqToCoCoEqℕ zero (suc m) ()
eqToCoCoEqℕ (suc n) zero ()
eqToCoCoEqℕ (suc n) (suc m) eq = eqToCoCoEqℕ n m eq

CoCoEq : (a : U) → El a → El a → Type₀

CoCoEq nat' x y = CoCoEqℕ x y
CoCoEq top' _ _ = Unit
CoCoEq bot' _ _ = Unit
CoCoEq (pi' a b) f g = (x : El a) → CoCoEq (b x) (f x) (g x)
CoCoEq (sig' a b) (x , y) (x' , y') =
  Σ (Eq a x x') (λ e →
      CoCoEq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e) y) y')

cocoToEq : (a : U) → (x y : El a) → CoCoEq a x y → Eq a x y
cocoToEq nat' x y cc = cocoToEqℕ x y cc
cocoToEq top' _ _ _ = tt
cocoToEq bot' () _ _
cocoToEq (pi' a b) f g cc =
  λ x → cocoToEq (b x) (f x) (g x) (cc x)
cocoToEq (sig' a b) (x , y) (x' , y') (e , cc-snd) =
  e , cocoToEq (b x') _ _ cc-snd

eqToCoCoEq : (a : U) → (x y : El a) → Eq a x y → CoCoEq a x y
eqToCoCoEq nat' x y eq = eqToCoCoEqℕ x y eq
eqToCoCoEq top' _ _ _ = tt
eqToCoCoEq bot' () _ _
eqToCoCoEq (pi' a b) f g eq =
  λ x → eqToCoCoEq (b x) (f x) (g x) (eq x)
eqToCoCoEq (sig' a b) (x , y) (x' , y') (eq-fst , eq-snd) =
  eq-fst
  , eqToCoCoEq (b x') _ _ eq-snd
