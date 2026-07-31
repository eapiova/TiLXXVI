{-# OPTIONS --cubical --safe #-}

module HObsTT.Apartness where

open import Cubical.Foundations.Prelude renaming (sym to pathSym)
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.Incompatibility

irrefl : (a : U) → (x : El a) → CoEq a x x → ⊥
irrefl a x co = incomp a x x co (eqRefl a x)

-- Strength of apartness: `CoEq a x y` refutes a path `x ≡ y`.
-- Previously the standalone `Strength.agda`; folded in here.
strength : (a : U) → (x y : El a) → CoEq a x y → x ≡ y → ⊥
strength a x y co p =
  incomp a x y co (subst (Eq a x) p (eqRefl a x))

symℕ : (n m : ℕ) → CoEq nat' n m → CoEq nat' m n
symℕ zero zero ()
symℕ zero (suc m) _ = tt
symℕ (suc n) zero _ = tt
symℕ (suc n) (suc m) co = symℕ n m co

sym : (a : U) → (x y : El a) → CoEq a x y → CoEq a y x
sym nat' n m co = symℕ n m co
sym top' _ _ ()
sym bot' () _ _
sym (pi' a b) f g (x , co) =
  x , sym (b x) (f x) (g x) co
sym (sig' a b) (x , y) (x' , y') co e' = co-snd'
  where
    p : x' ≡ x
    p = eqToPath a x' x e'

    codePath : b x' ≡ b x
    codePath = cong b p

    co-snd : CoEq (b x') (subst (λ z → El (b z)) (pathSym p) y) y'
    co-snd =
      subst
        (λ z → CoEq (b x') z y')
        (cong
          (λ q → subst (λ z → El (b z)) q y)
          (eqToPathSym a x' x e'))
        (co (eqSym a x' x e'))

    co-snd-sym : CoEq (b x') y' (subst (λ z → El (b z)) (pathSym p) y)
    co-snd-sym = sym (b x') (subst (λ z → El (b z)) (pathSym p) y) y' co-snd

    co-snd-code : CoEq (b x)
      (subst El codePath y')
      (subst El codePath (subst (λ z → El (b z)) (pathSym p) y))
    co-snd-code = coEqChangeCode codePath co-snd-sym

    co-snd' : CoEq (b x)
      (subst (λ z → El (b z)) p y')
      y
    co-snd' =
      subst
        (λ z → CoEq (b x) (subst (λ z → El (b z)) p y') z)
        (substSubst⁻ El codePath y)
        co-snd-code

-- Proof relevance: at function codes, distinct counterexample points give
-- distinct co-identity proofs, so `CoEq` has no `eqIsProp` analogue.
coEqPiNotProp :
  isProp (CoEq (pi' nat' (λ _ → nat')) (λ _ → zero) (λ _ → suc zero)) → ⊥
coEqPiNotProp h = znots (cong fst (h (zero , tt) (suc zero , tt)))
