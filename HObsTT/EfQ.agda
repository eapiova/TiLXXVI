{-# OPTIONS --cubical --safe #-}

-- KP Proposition 2.9 (EfQ) for HObsTT.
--
-- In HObsTT, the "atoms" at the propositional level are Eq a x y (and
-- CoEq a x y) for specific a : U, x y : El a. Crucially, these atoms are
-- COMPUTED by structural recursion on a, so their base cases are Unit, ⊥,
-- or structural combinations thereof. Consequently, ⊥ → Eq a x y holds
-- unconditionally for every universe code and every pair of elements —
-- no atomic assumption is needed, in contrast to the PL case.
--
-- This is a structural advantage of the HObsTT framing: the KP restricted
-- ex falso becomes vacuously total at Eq atoms. The same holds for CoEq.

module HObsTT.EfQ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq

-- ------------------------------------------------------------
-- Eq: unconditional ⊥ → Eq a x y
-- ------------------------------------------------------------

EfQ-Eqℕ : (x y : ℕ) → ⊥ → Eqℕ x y
EfQ-Eqℕ zero    zero    _ = tt
EfQ-Eqℕ zero    (suc _) b = b
EfQ-Eqℕ (suc _) zero    b = b
EfQ-Eqℕ (suc x) (suc y) b = EfQ-Eqℕ x y b

EfQ-Eq : (a : U) (x y : El a) → ⊥ → Eq a x y
EfQ-Eq nat' x y                            b = EfQ-Eqℕ x y b
EfQ-Eq top' _ _                            _ = tt
EfQ-Eq bot' _ _                            _ = tt
EfQ-Eq (pi' a b) f g                       x =
  λ y → EfQ-Eq (b y) (f y) (g y) x
EfQ-Eq (sig' a b) (x , y) (x' , y')        w =
  let e = EfQ-Eq a x x' w
  in e , EfQ-Eq (b x')
           (subst (λ z → El (b z)) (eqToPath a x x' e) y) y' w

-- ------------------------------------------------------------
-- Inhabitation from ⊥: every decoded type is ⊥-inhabitable by code
-- recursion, with no use of Empty.rec (the bot' clause returns the
-- hypothesis itself, since El bot' = ⊥).
-- ------------------------------------------------------------

inhab : (a : U) → ⊥ → El a
inhab nat'          _ = zero
inhab top'          _ = tt
inhab bot'          b = b
inhab (pi' a b)     w = λ x → inhab (b x) w
inhab (sig' a b)    w = inhab a w , inhab (b (inhab a w)) w

-- ------------------------------------------------------------
-- CoEq: unconditional ⊥ → CoEq a x y
-- ------------------------------------------------------------
-- The pi' case must pick an element of El a for the Σ witness — the one
-- point where EfQ must CONSTRUCT data rather than merely follow the
-- clause structure. The witness is supplied by inhab, so the proof is
-- Empty.rec-free. The genuine Eq/CoEq asymmetry under minimal logic is
-- therefore one of inhabitation, not of eliminators: EfQ-Eq needs no
-- inhabitation of El at all, while EfQ-CoEq needs ⊥-inhabitation of the
-- Π-domain — available universe-internally here (inhab), but a real
-- assumption in any setting where El is opaque.

EfQ-CoEqℕ : (x y : ℕ) → ⊥ → CoEqℕ x y
EfQ-CoEqℕ zero    zero    b = b
EfQ-CoEqℕ zero    (suc _) _ = tt
EfQ-CoEqℕ (suc _) zero    _ = tt
EfQ-CoEqℕ (suc x) (suc y) b = EfQ-CoEqℕ x y b

EfQ-CoEq : (a : U) (x y : El a) → ⊥ → CoEq a x y
EfQ-CoEq nat' x y                          b = EfQ-CoEqℕ x y b
EfQ-CoEq top' _ _                          b = b
EfQ-CoEq bot' _ _                          b = b
EfQ-CoEq (pi' a b) f g                     w =
  inhab a w , EfQ-CoEq (b (inhab a w)) (f (inhab a w)) (g (inhab a w)) w
EfQ-CoEq (sig' a b) (x , y) (x' , y')      w =
  λ e → EfQ-CoEq (b x')
         (subst (λ z → El (b z)) (eqToPath a x x' e) y) y' w
