{-# OPTIONS --cubical --safe #-}

module HObsTT.CoEq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import HObsTT.Universe
open import HObsTT.Eq

-- ============================================================
-- Co-identity (observational apartness) by DUAL structural
-- recursion on universe codes.
--
-- The recipe: apply Köpp–Petrakis (·)^N to the Eq clauses.
--   Π ↦ Σ      (∀ ↦ ∃)
--   dependent Σ clauses dualize by turning the Eq witness ∃ into ∀
--   × ↦ ⊎      (∧ ↦ ∨)
--   ⊤ ↦ ⊥ and ⊥ ↦ ⊤   (negation of base cases)
-- ============================================================

CoEqℕ : ℕ → ℕ → Type₀
CoEqℕ zero zero       = ⊥
CoEqℕ zero (suc m)    = Unit
CoEqℕ (suc n) zero    = Unit
CoEqℕ (suc n) (suc m) = CoEqℕ n m

CoEq : (a : U) → El a → El a → Type₀

CoEq nat' x y = CoEqℕ x y
CoEq top' _ _ = ⊥
CoEq bot' _ _ = ⊥
CoEq (pi' a b) f g = Σ (El a) (λ x → CoEq (b x) (f x) (g x))
CoEq (sig' a b) (x , y) (x' , y') =
  (e : Eq a x x') →
  CoEq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e) y) y'

coEqChangeCode : {a a' : U} → (p : a ≡ a') → {x y : El a}
  → CoEq a x y → CoEq a' (subst El p x) (subst El p y)
coEqChangeCode {a = a} p {x} {y} =
  J
    (λ a' p' → CoEq a x y → CoEq a' (subst El p' x) (subst El p' y))
    (λ co →
      subst2
        (λ u v → CoEq a u v)
        (sym (transportRefl x))
        (sym (transportRefl y))
        co)
    p
