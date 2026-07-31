{-# OPTIONS --cubical --safe #-}

module HObsTT.Incompatibility where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq

-- ============================================================
-- THE KEY THEOREM: Eq and CoEq are mutually exclusive.
--
-- This is the analogue of Köpp–Petrakis Lemma 4.3:
--   A^N → A → B   (specialized to B = ⊥)
--
-- Proof: by induction on the universe code a.
-- ============================================================

incompℕ : (n m : ℕ) → CoEq nat' n m → Eq nat' n m → ⊥
incompℕ zero zero co eq = co
incompℕ zero (suc m) co eq = eq
incompℕ (suc n) zero co eq = eq
incompℕ (suc n) (suc m) co eq = incompℕ n m co eq

incomp : (a : U) → (x y : El a) → CoEq a x y → Eq a x y → ⊥

-- ℕ cases
incomp nat' n m co eq = incompℕ n m co eq

-- ⊤
incomp top' _ _ co _ = co  -- co : ⊥

-- ⊥ (vacuous)
incomp bot' () _ _ _

-- Π: co = (x , witness), eq = pointwise proof
-- Project x from co, apply eq at x, use IH
incomp (pi' a b) f g (x , cofx-gx) eq =
  incomp (b x) (f x) (g x) cofx-gx (eq x)

-- Σ: apply the co-witness to the Eq witness and recurse on the second component
incomp (sig' a b) (x , y) (x' , y') co (eq-fst , eq-snd) =
  incomp
    (b x')
    (subst (λ z → El (b z)) (eqToPath a x x' eq-fst) y)
    y'
    (co eq-fst)
    eq-snd
