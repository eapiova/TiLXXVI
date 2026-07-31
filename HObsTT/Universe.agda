{-# OPTIONS --cubical --safe #-}

module HObsTT.Universe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty

-- Tarski-style universe of codes
-- Keep this minimal. Add codes only when needed.

data U : Type₀
El : U → Type₀

data U where
  nat'   : U
  top'   : U
  bot'   : U
  pi'    : (a : U) → (El a → U) → U
  sig'   : (a : U) → (El a → U) → U

El nat'       = ℕ
El top'       = Unit
El bot'       = ⊥
El (pi' a b)  = (x : El a) → El (b x)
El (sig' a b) = Σ (El a) (λ x → El (b x))
