{-# OPTIONS --cubical --safe #-}

-- Every code of the prototype is a TIGHT strong set.
--
-- KP call (X, =_X, ≠_X) a strong set when the inequality coincides with the
-- strong inequality (=_X)^N; our types are strong sets by construction, since
-- CoEq is definitionally the KP dual of Eq. KP further call the equality
-- tight when ¬(x ≠ y) → x = y. In the partial setting of TCF "very few
-- non-trivial formulas will be tight"; in our total setting tightness is
-- GLOBAL: tightEq below proves ¬ CoEq a x y → Eq a x y at every code, by
-- induction on codes mutually with ¬¬-stability of Eq (stableEq).
--
-- Contrast: the dual direction ¬ Eq → CoEq (EqCoTight, AUC.agda) is NOT
-- global — at the function code it is Markov-style witness extraction.

module HObsTT.Tightness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum renaming (inl to inl'; inr to inr')
open import Cubical.Data.Sigma
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.EfQ
open import HObsTT.Cotransitivity using (decEqℕ)

-- ------------------------------------------------------------
-- ¬¬-stability of observational equality, by induction on codes.
-- ------------------------------------------------------------

stableEqℕ : (x y : ℕ) → ((Eqℕ x y → ⊥) → ⊥) → Eqℕ x y
stableEqℕ x y h with decEqℕ x y
... | inl' e  = e
... | inr' ne = EfQ-Eqℕ x y (h ne)

stableEq : (a : U) (x y : El a) → ((Eq a x y → ⊥) → ⊥) → Eq a x y
stableEq nat' x y h = stableEqℕ x y h
stableEq top' _ _ _ = tt
stableEq bot' _ _ _ = tt
stableEq (pi' a b) f g h =
  λ x → stableEq (b x) (f x) (g x) (λ nfx → h (λ e → nfx (e x)))
stableEq (sig' a b) (x , y) (x' , y') h = e₀ , d
  where
  e₀ : Eq a x x'
  e₀ = stableEq a x x' (λ ne → h (λ { (e , _) → ne e }))

  d : Eq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e₀) y) y'
  d = stableEq (b x') _ y'
        (λ nd → h (λ { (e , d') → nd (alignEqWitness a b e e₀ d') }))

-- ------------------------------------------------------------
-- Global tightness: ¬ CoEq → Eq at every code.
-- ------------------------------------------------------------

tightEqℕ : (x y : ℕ) → (CoEqℕ x y → ⊥) → Eqℕ x y
tightEqℕ zero    zero    _ = tt
tightEqℕ zero    (suc _) h = h tt
tightEqℕ (suc _) zero    h = h tt
tightEqℕ (suc x) (suc y) h = tightEqℕ x y h

tightEq : (a : U) (x y : El a) → (CoEq a x y → ⊥) → Eq a x y
tightEq nat' x y h = tightEqℕ x y h
tightEq top' _ _ _ = tt
tightEq bot' _ _ _ = tt
tightEq (pi' a b) f g h =
  λ x → tightEq (b x) (f x) (g x) (λ d → h (x , d))
tightEq (sig' a b) (x , y) (x' , y') h = e₀ , d
  where
  e₀ : Eq a x x'
  e₀ = stableEq a x x'
         (λ ne → h (λ e → EfQ-CoEq (b x') _ y' (ne e)))

  d : Eq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e₀) y) y'
  d = tightEq (b x') _ y'
        (λ dco → h (λ e →
            subst (λ q → CoEq (b x')
                           (subst (λ z → El (b z)) (eqToPath a x x' q) y) y')
                  (eqIsProp a x x' e₀ e)
                  dco))
