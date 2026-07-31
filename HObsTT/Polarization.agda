{-# OPTIONS --cubical --safe #-}

-- The polarized square, derived.
--
-- Implication, the two products, and the sum are DEFINED codes over the
-- existing universe (constant-family Π/Σ and two-point-indexed Π/Σ, with
-- the two-point code derived from ℕ); nothing is added.  Their computed
-- duals reproduce the SNPolarization table at the equality level:
--
--   Imp    A B  (constant Π)   dual: Tensor-shape  (counterexample pair)
--   Tensor A B  (constant Σ)   dual: Imp-shape     (Eq → CoEq)
--   With   A B  (Bool-Π)       dual: Plus-shape    (a side that differs)
--   Plus   A B  (Bool-Σ)       dual: tag-wise      (as the primitive sum)
--
-- To define is to choose a presentation, and the dual follows the
-- presentation.  The wrapper of Cotransitivity.agda is definitionally the
-- Tensor unit (wrapperIsTensorUnit); the With unit instead exposes the
-- positive disagreement (withUnitDual), so the MP∨ calibration measures
-- the multiplicative/additive gap at the unit.

module HObsTT.Polarization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum renaming (inl to inl'; inr to inr')
open import Cubical.Data.Sigma
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.EfQ
open import HObsTT.Cotransitivity using
  ( Cotrans
  ; EqDecidable
  ; decEqℕ
  ; cotransPi
  ; cotransSigDecidable
  ; F
  ; S
  )

-- ------------------------------------------------------------
-- The derived codes.
-- ------------------------------------------------------------

P : ℕ → U
P zero          = top'
P (suc zero)    = top'
P (suc (suc _)) = bot'

𝔹 : U
𝔹 = sig' nat' P

leftB rightB : El 𝔹
leftB  = zero , tt
rightB = suc zero , tt

fam : U → U → El 𝔹 → U
fam A B (zero , _)          = A
fam A B (suc zero , _)      = B
fam A B (suc (suc _) , ())

Imp Tensor With Plus : U → U → U
Imp    A B = pi'  A (λ _ → B)
Tensor A B = sig' A (λ _ → B)
With   A B = pi'  𝔹 (fam A B)
Plus   A B = sig' 𝔹 (fam A B)

-- ------------------------------------------------------------
-- Cotransitivity of the additive codes.
-- ------------------------------------------------------------

decEq𝔹 : EqDecidable 𝔹
decEq𝔹 (n , p) (zero , q) with decEqℕ n zero
... | inl' e  = inl' (e , tt)
... | inr' ¬e = inr' λ e' → ¬e (e' .fst)
decEq𝔹 (n , p) (suc zero , q) with decEqℕ n (suc zero)
... | inl' e  = inl' (e , tt)
... | inr' ¬e = inr' λ e' → ¬e (e' .fst)
decEq𝔹 _ (suc (suc _) , ())

private
  cotransFam : {A B : U} → Cotrans A → Cotrans B
    → (b : El 𝔹) → Cotrans (fam A B b)
  cotransFam cA cB (zero , _)          = cA
  cotransFam cA cB (suc zero , _)      = cB
  cotransFam cA cB (suc (suc _) , ())

cotransPlus : {A B : U}
  → Cotrans A → Cotrans B → Cotrans (Plus A B)
cotransPlus cA cB =
  cotransSigDecidable decEq𝔹 (cotransFam cA cB)

cotransWith : {A B : U}
  → Cotrans A → Cotrans B → Cotrans (With A B)
cotransWith cA cB =
  cotransPi (cotransFam cA cB)

-- ------------------------------------------------------------
-- Imp row: definitional.
-- ------------------------------------------------------------

coEqImp : (A B : U) (f g : El (Imp A B)) →
  CoEq (Imp A B) f g ≡ Σ (El A) (λ x → CoEq B (f x) (g x))
coEqImp A B f g = refl

-- ------------------------------------------------------------
-- Tensor row: the multiplicative refutation Eq → CoEq, up to the
-- trivial transport along a constant family.
-- ------------------------------------------------------------

tensorDual→ : (A B : U) {x x' : El A} {y y' : El B}
  → CoEq (Tensor A B) (x , y) (x' , y')
  → Eq A x x' → CoEq B y y'
tensorDual→ A B {y = y} {y' = y'} co e =
  subst (λ z → CoEq B z y') (transportRefl y) (co e)

tensorDual← : (A B : U) {x x' : El A} {y y' : El B}
  → (Eq A x x' → CoEq B y y')
  → CoEq (Tensor A B) (x , y) (x' , y')
tensorDual← A B {y = y} {y' = y'} h e =
  subst (λ z → CoEq B z y') (sym (transportRefl y)) (h e)

-- ------------------------------------------------------------
-- With row: the additive refutation, a side that differs.
-- ------------------------------------------------------------

withDual→ : (A B : U) (f g : El (With A B))
  → CoEq (With A B) f g
  → CoEq A (f leftB) (g leftB) ⊎ CoEq B (f rightB) (g rightB)
withDual→ A B f g ((zero , _) , d)          = inl' d
withDual→ A B f g ((suc zero , _) , d)      = inr' d
withDual→ A B f g ((suc (suc _) , ()) , _)

withDual← : (A B : U) (f g : El (With A B))
  → CoEq A (f leftB) (g leftB) ⊎ CoEq B (f rightB) (g rightB)
  → CoEq (With A B) f g
withDual← A B f g (inl' d) = leftB  , d
withDual← A B f g (inr' d) = rightB , d

-- ------------------------------------------------------------
-- Plus row: tag-wise, exactly as the primitive sum.
-- ------------------------------------------------------------

private
  fixInl : (A B : U) (u : El A) (e : Eq 𝔹 leftB leftB) →
    subst (λ b → El (fam A B b)) (eqToPath 𝔹 leftB leftB e) u ≡ u
  fixInl A B u e =
    cong (λ p → subst (λ b → El (fam A B b)) p u)
         (elIsSet 𝔹 leftB leftB (eqToPath 𝔹 leftB leftB e) refl)
    ∙ transportRefl u

  fixInr : (A B : U) (v : El B) (e : Eq 𝔹 rightB rightB) →
    subst (λ b → El (fam A B b)) (eqToPath 𝔹 rightB rightB e) v ≡ v
  fixInr A B v e =
    cong (λ p → subst (λ b → El (fam A B b)) p v)
         (elIsSet 𝔹 rightB rightB (eqToPath 𝔹 rightB rightB e) refl)
    ∙ transportRefl v

plusDualInl→ : (A B : U) (u u' : El A)
  → CoEq (Plus A B) (leftB , u) (leftB , u') → CoEq A u u'
plusDualInl→ A B u u' co =
  let e = eqRefl 𝔹 leftB in
  subst (λ z → CoEq A z u') (fixInl A B u e) (co e)

plusDualInl← : (A B : U) (u u' : El A)
  → CoEq A u u' → CoEq (Plus A B) (leftB , u) (leftB , u')
plusDualInl← A B u u' d e =
  subst (λ z → CoEq A z u') (sym (fixInl A B u e)) d

plusDualInr→ : (A B : U) (v v' : El B)
  → CoEq (Plus A B) (rightB , v) (rightB , v') → CoEq B v v'
plusDualInr→ A B v v' co =
  let e = eqRefl 𝔹 rightB in
  subst (λ z → CoEq B z v') (fixInr A B v e) (co e)

plusDualInr← : (A B : U) (v v' : El B)
  → CoEq B v v' → CoEq (Plus A B) (rightB , v) (rightB , v')
plusDualInr← A B v v' d e =
  subst (λ z → CoEq B z v') (sym (fixInr A B v e)) d

plusDualMixed : (A B : U) (u : El A) (v : El B)
  → CoEq (Plus A B) (leftB , u) (rightB , v)
plusDualMixed A B u v e = EfQ-CoEq B _ v (e .fst)

-- ------------------------------------------------------------
-- The two products have equivalent carriers.
-- ------------------------------------------------------------

tensorWithCarrier : (A B : U) → Iso (El (Tensor A B)) (El (With A B))
tensorWithCarrier A B =
  iso to from sec ret
  where
  to : El (Tensor A B) → El (With A B)
  to (a , b) (zero , _)          = a
  to (a , b) (suc zero , _)      = b
  to (a , b) (suc (suc _) , ())

  from : El (With A B) → El (Tensor A B)
  from f = f leftB , f rightB

  sec : ∀ f → to (from f) ≡ f
  sec f = funExt λ
    { (zero , _)          → refl
    ; (suc zero , _)      → refl
    ; (suc (suc _) , ())
    }

  ret : ∀ p → from (to p) ≡ p
  ret (a , b) = refl

-- ------------------------------------------------------------
-- Units: the wrapper of the MP∨ calibration is the Tensor unit,
-- definitionally; the With unit exposes the positive disagreement.
-- ------------------------------------------------------------

wrapperIsTensorUnit : S ≡ Tensor F top'
wrapperIsTensorUnit = refl

withUnitDual→ : (A : U) (f g : El (With A top'))
  → CoEq (With A top') f g → CoEq A (f leftB) (g leftB)
withUnitDual→ A f g co with withDual→ A top' f g co
... | inl' d = d
... | inr' d = EfQ-CoEq A _ _ d

withUnitDual← : (A : U) (f g : El (With A top'))
  → CoEq A (f leftB) (g leftB) → CoEq (With A top') f g
withUnitDual← A f g d = withDual← A top' f g (inl' d)
