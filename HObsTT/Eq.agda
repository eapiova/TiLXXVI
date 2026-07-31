{-# OPTIONS --cubical --safe #-}

module HObsTT.Eq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties
open import HObsTT.Universe

-- Observational equality by structural recursion on universe codes.
-- Follows HObsTT: equality of functions is pointwise, of pairs is
-- componentwise (with transport).

Eqℕ : ℕ → ℕ → Type₀
Eqℕ zero zero       = Unit
Eqℕ zero (suc m)    = ⊥
Eqℕ (suc n) zero    = ⊥
Eqℕ (suc n) (suc m) = Eqℕ n m

eqReflℕ : (n : ℕ) → Eqℕ n n
eqReflℕ zero    = tt
eqReflℕ (suc n) = eqReflℕ n

eqToPathℕ : (n m : ℕ) → Eqℕ n m → n ≡ m
eqToPathℕ zero zero _ = refl
eqToPathℕ zero (suc m) ()
eqToPathℕ (suc n) zero ()
eqToPathℕ (suc n) (suc m) e = cong suc (eqToPathℕ n m e)

pathToEqℕ : (n m : ℕ) → n ≡ m → Eqℕ n m
pathToEqℕ n m p = J (λ m _ → Eqℕ n m) (eqReflℕ n) p

eqIsPropℕ : (n m : ℕ) → isProp (Eqℕ n m)
eqIsPropℕ zero zero = isPropUnit
eqIsPropℕ zero (suc m) = isProp⊥
eqIsPropℕ (suc n) zero = isProp⊥
eqIsPropℕ (suc n) (suc m) = eqIsPropℕ n m

eqSymℕ : (n m : ℕ) → Eqℕ n m → Eqℕ m n
eqSymℕ zero zero _ = tt
eqSymℕ zero (suc m) ()
eqSymℕ (suc n) zero ()
eqSymℕ (suc n) (suc m) e = eqSymℕ n m e

elIsSet : (a : U) → isSet (El a)
elIsSet nat' = isSetℕ
elIsSet top' = isSetUnit
elIsSet bot' = isProp→isSet isProp⊥
elIsSet (pi' a b) = isSetΠ λ x → elIsSet (b x)
elIsSet (sig' a b) = isSetΣ (elIsSet a) λ x → elIsSet (b x)

mutual
  Eq : (a : U) → El a → El a → Type₀

  Eq nat' x y = Eqℕ x y
  Eq top' _ _ = Unit
  Eq bot' _ _ = Unit
  Eq (pi' a b) f g = (x : El a) → Eq (b x) (f x) (g x)
  Eq (sig' a b) (x , y) (x' , y') =
    Σ (Eq a x x') λ e →
      Eq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e) y) y'

  eqToPath : (a : U) → (x y : El a) → Eq a x y → x ≡ y

  eqToPath nat' x y e = eqToPathℕ x y e
  eqToPath top' _ _ _ = refl
  eqToPath bot' () _ _
  eqToPath (pi' a b) f g e =
    funExt λ x → eqToPath (b x) (f x) (g x) (e x)
  eqToPath (sig' a b) (x , y) (x' , y') (e , e₂) =
    ΣPathTransport→PathΣ (x , y) (x' , y')
      ( eqToPath a x x' e
      , eqToPath (b x')
          (subst (λ z → El (b z)) (eqToPath a x x' e) y)
          y'
          e₂
      )

  pathToEq : (a : U) → (x y : El a) → x ≡ y → Eq a x y

  eqToPathPathToEq : (a : U) → (x y : El a) → (p : x ≡ y) →
    eqToPath a x y (pathToEq a x y p) ≡ p

  pathToEq nat' x y p = pathToEqℕ x y p
  pathToEq top' _ _ _ = tt
  pathToEq bot' () _ _
  pathToEq (pi' a b) f g p =
    λ x → pathToEq (b x) (f x) (g x) (funExt⁻ p x)
  pathToEq (sig' a b) (x , y) (x' , y') p =
    let q = PathΣ→ΣPathTransport (x , y) (x' , y') p in
    pathToEq a x x' (q .fst)
      , subst
          (λ z → Eq (b x') z y')
          (cong
            (λ r → subst (λ z → El (b z)) r y)
            (sym (eqToPathPathToEq a x x' (q .fst))))
          (pathToEq (b x')
            (subst (λ z → El (b z)) (q .fst) y)
            y'
            (q .snd))

  eqIsProp : (a : U) → (x y : El a) → isProp (Eq a x y)

  eqIsProp nat' x y = eqIsPropℕ x y
  eqIsProp top' _ _ = isPropUnit
  eqIsProp bot' () _ 
  eqIsProp (pi' a b) f g =
    isPropΠ λ x → eqIsProp (b x) (f x) (g x)
  eqIsProp (sig' a b) (x , y) (x' , y') =
    isPropΣ (eqIsProp a x x')
      (λ e → eqIsProp (b x') (subst (λ z → El (b z)) (eqToPath a x x' e) y) y')

  eqToPathPathToEq a x y p =
    elIsSet a x y (eqToPath a x y (pathToEq a x y p)) p

eqRefl : (a : U) → (x : El a) → Eq a x x
eqRefl a x = pathToEq a x x refl

eqSym : (a : U) → (x y : El a) → Eq a x y → Eq a y x
eqSym a x y e = pathToEq a y x (sym (eqToPath a x y e))

eqToPathSym : (a : U) → (x y : El a) → (e : Eq a x y) →
  eqToPath a y x (eqSym a x y e) ≡ sym (eqToPath a x y e)
eqToPathSym a x y e = eqToPathPathToEq a y x (sym (eqToPath a x y e))

eqChangeCode : {a a' : U} → (p : a ≡ a') → {x y : El a}
  → Eq a x y → Eq a' (subst El p x) (subst El p y)
eqChangeCode {a = a} {a' = a'} p {x} {y} e =
  pathToEq a' (subst El p x) (subst El p y) (cong (subst El p) (eqToPath a x y e))

alignEqWitness :
  (a : U) (b : El a → U) →
  {x x' : El a} {y : El (b x)} {y' : El (b x')} →
  (e e' : Eq a x x') →
  Eq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e) y) y' →
  Eq (b x') (subst (λ z → El (b z)) (eqToPath a x x' e') y) y'
alignEqWitness a b {x} {x'} {y} {y'} e e' =
  subst
    (λ z → Eq (b x') z y')
    (cong (λ q → subst (λ w → El (b w)) (eqToPath a x x' q) y)
      (eqIsProp a x x' e e'))
