{-# OPTIONS --cubical --safe #-}

-- Axiom of Unique Choice against observational Eq / CoEq.
--
-- In this prototype, existence is an untruncated Sigma, so the selector is
-- its first projection.  The uniqueness proof is nevertheless useful: it
-- proves that observationally equal inputs have observationally equal chosen
-- outputs, and incompatibility then gives the contrapositive
--
--   CoEq b (f x) (f x') -> Eq a x x' -> bottom.
--
-- The intended full bilateral theory is designed to make the last step to
-- CoEq a x x' automatic through a strong Pi carrying co-ap.  Here
-- El (pi' a b) is an ordinary Agda function type, so co-ap is not present.  We expose
-- a sufficient uniform bridge as EqCoTight and prove the positive result when
-- it is available; nat' supplies a concrete unconditional instance.

module HObsTT.AUC where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.Incompatibility

-- A chosen witness together with Eq-uniqueness among all witnesses.
UniqueAt :
  {a b : U} (R : El a → El b → Type₀) →
  El a → El b → Type₀
UniqueAt {b = b} R x y =
  R x y × ((y' : El b) → R x y' → Eq b y y')

UniqueExists :
  {a b : U} (R : El a → El b → Type₀) → Type₀
UniqueExists {a = a} {b = b} R =
  (x : El a) → Σ (El b) (UniqueAt R x)

Choice :
  {a b : U} (R : El a → El b → Type₀) → Type₀
Choice {a = a} {b = b} R =
  Σ (El a → El b) λ f → (x : El a) → R x (f x)

choiceFunction :
  {a b : U} {R : El a → El b → Type₀} →
  UniqueExists R → El a → El b
choiceFunction uniqueExists x = uniqueExists x .fst

choiceSatisfies :
  {a b : U} {R : El a → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  (x : El a) → R x (choiceFunction uniqueExists x)
choiceSatisfies uniqueExists x = uniqueExists x .snd .fst

choiceUnique :
  {a b : U} {R : El a → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  (x : El a) (y : El b) →
  R x y → Eq b (choiceFunction uniqueExists x) y
choiceUnique uniqueExists x = uniqueExists x .snd .snd

-- Ordinary AUC is projection because UniqueExists uses an untruncated Sigma.
auc :
  {a b : U} {R : El a → El b → Type₀} →
  UniqueExists R → Choice R
auc uniqueExists =
  choiceFunction uniqueExists , choiceSatisfies uniqueExists

-- Uniqueness supplies observational Eq-extensionality of the selector.
-- The witness at x' is transported back along Eq a x x' before uniqueness
-- is applied in the fiber over x.
aucRespectsEq :
  {a b : U} {R : El a → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  (x x' : El a) →
  Eq a x x' →
  Eq b (choiceFunction uniqueExists x) (choiceFunction uniqueExists x')
aucRespectsEq {a = a} {R = R} uniqueExists x x' e =
  choiceUnique uniqueExists x (choiceFunction uniqueExists x')
    (subst
      (λ z → R z (choiceFunction uniqueExists x'))
      (sym (eqToPath a x x' e))
      (choiceSatisfies uniqueExists x'))

-- Transport in a constant family is propositionally the identity.  Keeping
-- this alignment explicit lets the graph lemmas below unfold the corrected
-- Pi-shaped CoEq clause for Sigma codes directly.
private
  substConstPath :
    {A X : Type₀} {x x' : A} →
    (p : x ≡ x') (z : X) → subst (λ _ → X) p z ≡ z
  substConstPath {A = A} {X = X} {x = x} p z =
    J
      (λ x' p' → subst (λ _ → X) p' z ≡ z)
      (transportRefl z)
      p

choiceGraph :
  {a b : U} {R : El a → El b → Type₀} →
  UniqueExists R → El a → El (sig' a (λ _ → b))
choiceGraph uniqueExists x = x , choiceFunction uniqueExists x

-- Input Eq and uniqueness make the selected graph points observationally
-- equal.  The second component is exactly aucRespectsEq, aligned with the
-- constant-family transport appearing in Eq's Sigma clause.
aucGraphEq :
  {a b : U} {R : El a → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  (x x' : El a) → Eq a x x' →
  Eq (sig' a (λ _ → b))
    (choiceGraph uniqueExists x)
    (choiceGraph uniqueExists x')
aucGraphEq {a = a} {b = b} uniqueExists x x' e =
  e ,
  subst
    (λ z → Eq b z (choiceFunction uniqueExists x'))
    (sym (substConstPath
      (eqToPath a x x' e)
      (choiceFunction uniqueExists x)))
    (aucRespectsEq uniqueExists x x' e)

-- Output CoEq makes the graph points co-equal.  This materially uses the
-- corrected KP-faithful Sigma clause: after unfolding, the goal is a Pi over
-- every e : Eq a x x', not a disjunction requiring a tightness decision.
aucGraphCoEq :
  {a b : U} {R : El a → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  (x x' : El a) →
  CoEq b (choiceFunction uniqueExists x) (choiceFunction uniqueExists x') →
  CoEq (sig' a (λ _ → b))
    (choiceGraph uniqueExists x)
    (choiceGraph uniqueExists x')
aucGraphCoEq {a = a} {b = b} uniqueExists x x' co e =
  subst
    (λ z → CoEq b z (choiceFunction uniqueExists x'))
    (sym (substConstPath
      (eqToPath a x x' e)
      (choiceFunction uniqueExists x)))
    co

-- The unconditional conclusion established for an arbitrary domain in the
-- current raw-Agda Pi prototype: output co-identity refutes input equality.
aucCoExtIncompat :
  {a b : U} {R : El a → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  (x x' : El a) →
  CoEq b (choiceFunction uniqueExists x) (choiceFunction uniqueExists x') →
  Eq a x x' → ⊥
aucCoExtIncompat {a = a} {b = b} uniqueExists x x' co e =
  incomp
    (sig' a (λ _ → b))
    (choiceGraph uniqueExists x)
    (choiceGraph uniqueExists x')
    (aucGraphCoEq uniqueExists x x' co)
    (aucGraphEq uniqueExists x x' e)

-- The negative tightness direction needed to turn refuted Eq into positive
-- CoEq.  This is Legacy.RelTightAtom.tight₋ specialized to Eq / CoEq.
EqCoTight : U → Type₀
EqCoTight a =
  (x x' : El a) → (Eq a x x' → ⊥) → CoEq a x x'

-- The corrected Pi-shaped CoEq clause makes EqCoTight closed under Sigma
-- whenever every fiber has the property.  No decision between base and fiber
-- apartness, and therefore no tightness hypothesis for the base, is needed.
sigEqCoTight :
  {a : U} {b : El a → U} →
  ((x : El a) → EqCoTight (b x)) →
  EqCoTight (sig' a b)
sigEqCoTight {a = a} {b = b} fiberTight
  (x , y) (x' , y') notEq e =
  fiberTight x'
    (subst (λ z → El (b z)) (eqToPath a x x' e) y)
    y'
    (λ e' → notEq (e , e'))

StronglyExtensional :
  (a b : U) → (El a → El b) → Type₀
StronglyExtensional a b f =
  (x x' : El a) → CoEq b (f x) (f x') → CoEq a x x'

StrongChoice :
  {a b : U} (R : El a → El b → Type₀) → Type₀
StrongChoice {a = a} {b = b} R =
  Σ (El a → El b) λ f →
    ((x : El a) → R x (f x)) × StronglyExtensional a b f

aucStronglyExtensional :
  {a b : U} {R : El a → El b → Type₀} →
  EqCoTight a →
  (uniqueExists : UniqueExists R) →
  StronglyExtensional a b (choiceFunction uniqueExists)
aucStronglyExtensional tight uniqueExists x x' co =
  tight x x' (aucCoExtIncompat uniqueExists x x' co)

aucStrong :
  {a b : U} {R : El a → El b → Type₀} →
  EqCoTight a → UniqueExists R → StrongChoice R
aucStrong tight uniqueExists =
  choiceFunction uniqueExists ,
    choiceSatisfies uniqueExists ,
    aucStronglyExtensional tight uniqueExists

-- nat' is Eq/CoEq-tight by direct computation.  Kept in the HObsTT layer
-- rather than importing the equivalent legacy notEqToCoEqℕ lemma.
natEqCoTight : EqCoTight nat'
natEqCoTight zero zero notEq = notEq tt
natEqCoTight zero (suc m) notEq = tt
natEqCoTight (suc n) zero notEq = tt
natEqCoTight (suc n) (suc m) notEq = natEqCoTight n m notEq

aucStronglyExtensionalNat :
  {b : U} {R : ℕ → El b → Type₀} →
  (uniqueExists : UniqueExists R) →
  StronglyExtensional nat' b (choiceFunction uniqueExists)
aucStronglyExtensionalNat =
  aucStronglyExtensional natEqCoTight

aucStrongNat :
  {b : U} {R : ℕ → El b → Type₀} →
  UniqueExists R → StrongChoice R
aucStrongNat = aucStrong natEqCoTight
