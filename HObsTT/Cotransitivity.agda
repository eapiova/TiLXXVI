{-# OPTIONS --cubical --safe #-}

-- Cotransitivity of co-identity, calibrated.
--
-- Positive fragment: CoEq is cotransitive at nat', top', bot'; Π-codes
-- preserve cotransitivity (the Π case uses the existing
-- counterexample point); a dependent Σ-code is cotransitive whenever its
-- base has decidable Eq and every fiber is cotransitive.
--
-- Calibration: unrestricted cotransitivity is NOT constructively available.
-- For the trivial Σ-wrapper S = sig' F (λ _ → top') over F = ℕ → ℕ, the
-- Σ-clause degenerates to denial inequality, CoEq S (u,tt) (v,tt) = ¬ Eq F u v,
-- and cotransitivity at S yields the disjunctive Markov principle
--   ¬(A ∧ B) → ¬A ∨ ¬B   for Π⁰₁ statements A, B,
-- via interleaved streams (mpDisjFromCotransS below). MP∨ is not derivable
-- over strong extensions of higher-order Heyting arithmetic (Kohlenbach),
-- so cotransitivity fails to be provable already at this wrapper code.

module HObsTT.Cotransitivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt; isContrUnit)
open import Cubical.Data.Sum as Sum renaming (inl to inl'; inr to inr')
open import Cubical.Data.Sigma
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.EfQ
open import HObsTT.Apartness using (coEqPiNotProp)

-- ------------------------------------------------------------
-- Cotransitivity (the comparison property) at a code.
-- ------------------------------------------------------------

Cotrans : U → Type₀
Cotrans a = (x y z : El a) → CoEq a x y → CoEq a x z ⊎ CoEq a z y

-- ------------------------------------------------------------
-- Base codes.
-- ------------------------------------------------------------

cotransℕ : (x y z : ℕ) → CoEqℕ x y → CoEqℕ x z ⊎ CoEqℕ z y
cotransℕ zero    zero    _       ()
cotransℕ zero    (suc _) zero    _  = inr' tt
cotransℕ zero    (suc _) (suc _) _  = inl' tt
cotransℕ (suc _) zero    zero    _  = inl' tt
cotransℕ (suc _) zero    (suc _) _  = inr' tt
cotransℕ (suc x) (suc y) zero    _  = inl' tt
cotransℕ (suc x) (suc y) (suc z) co = cotransℕ x y z co

cotransNat : Cotrans nat'
cotransNat = cotransℕ

cotransTop : Cotrans top'
cotransTop _ _ _ ()

cotransBot : Cotrans bot'
cotransBot _ _ _ ()

-- ------------------------------------------------------------
-- Π-codes preserve cotransitivity: instantiate fiber cotransitivity at
-- the counterexample point carried by the co-identity witness.
-- ------------------------------------------------------------

cotransPi : {a : U} {b : El a → U}
  → ((x : El a) → Cotrans (b x)) → Cotrans (pi' a b)
cotransPi cb f g h (x₀ , d) with cb x₀ (f x₀) (g x₀) (h x₀) d
... | inl' d₁ = inl' (x₀ , d₁)
... | inr' d₂ = inr' (x₀ , d₂)

-- Example instance: the function code ℕ → ℕ is cotransitive.
cotransFun : Cotrans (pi' nat' (λ _ → nat'))
cotransFun = cotransPi (λ _ → cotransNat)

-- ------------------------------------------------------------
-- Dependent Σ-codes: cotransitive over bases with decidable equality.
-- ------------------------------------------------------------

EqDecidable : U → Type₀
EqDecidable a = (x y : El a) → Eq a x y ⊎ (Eq a x y → ⊥)

decEqℕ : (x y : ℕ) → Eqℕ x y ⊎ (Eqℕ x y → ⊥)
decEqℕ zero    zero    = inl' tt
decEqℕ zero    (suc _) = inr' λ b → b
decEqℕ (suc _) zero    = inr' λ b → b
decEqℕ (suc x) (suc y) = decEqℕ x y

decEqNat : EqDecidable nat'
decEqNat = decEqℕ

decEqTop : EqDecidable top'
decEqTop _ _ = inl' tt

decEqBot : EqDecidable bot'
decEqBot _ _ = inl' tt

cotransSigDecidable : {a : U} {b : El a → U}
  → EqDecidable a
  → ((x : El a) → Cotrans (b x))
  → Cotrans (sig' a b)
cotransSigDecidable {a} {b} dec cb (x , y) (x' , y') (x'' , y'') co
  with dec x x''
... | inr' ¬e = inl' λ e → EfQ-CoEq (b x'') _ y'' (¬e e)
... | inl' e₀ with dec x'' x'
...   | inr' ¬e' = inr' λ e' → EfQ-CoEq (b x') _ y' (¬e' e')
...   | inl' e₁ = branch (cb x' Y y' Z d₀)
  where
  B : El a → Type₀
  B z = El (b z)

  p₀ : x ≡ x''
  p₀ = eqToPath a x x'' e₀

  p₁ : x'' ≡ x'
  p₁ = eqToPath a x'' x' e₁

  e : Eq a x x'
  e = pathToEq a x x' (p₀ ∙ p₁)

  Y : B x'
  Y = subst B (p₀ ∙ p₁) y

  Z : B x'
  Z = subst B p₁ y''

  d₀ : CoEq (b x') Y y'
  d₀ = subst (λ q → CoEq (b x') (subst B q y) y')
             (eqToPathPathToEq a x x' (p₀ ∙ p₁))
             (co e)

  -- Left branch: pull the fiber apartness back to the fiber over x''.
  pulled : CoEq (b x') Y Z → CoEq (b x'') (subst B (sym p₁) Y) (subst B (sym p₁) Z)
  pulled = coEqChangeCode (cong b (sym p₁))

  fixL : subst B (sym p₁) Y ≡ subst B p₀ y
  fixL = cong (subst B (sym p₁)) (substComposite B p₀ p₁ y)
       ∙ substSubst⁻ B (sym p₁) (subst B p₀ y)

  fixR : subst B (sym p₁) Z ≡ y''
  fixR = substSubst⁻ B (sym p₁) y''

  branch : CoEq (b x') Y Z ⊎ CoEq (b x') Z y'
         → CoEq (sig' a b) (x , y) (x'' , y'') ⊎ CoEq (sig' a b) (x'' , y'') (x' , y')
  branch (inl' dYZ) =
    inl' λ e' →
      subst (λ q → CoEq (b x'') (subst B (eqToPath a x x'' q) y) y'')
            (eqIsProp a x x'' e₀ e')
            (subst2 (CoEq (b x'')) fixL fixR (pulled dYZ))
  branch (inr' dZ) =
    inr' λ e' →
      subst (λ q → CoEq (b x') (subst B (eqToPath a x'' x' q) y'') y')
            (eqIsProp a x'' x' e₁ e')
            dZ

-- ------------------------------------------------------------
-- Calibration: the trivial Σ-wrapper of ℕ → ℕ.
--
-- S is canonically isomorphic to F, but its Σ-clause computes co-identity
-- to DENIAL inequality of the base: CoEq S (u,tt) (v,tt) = ¬ Eq F u v.
-- Cotransitivity at S yields the disjunctive Markov principle.
-- ------------------------------------------------------------

F : U
F = pi' nat' (λ _ → nat')

S : U
S = sig' F (λ _ → top')

AllZero : El F → Type₀
AllZero α = (n : ℕ) → Eqℕ (α n) zero

MPdisj : Type₀
MPdisj = (α β : El F)
  → ((AllZero α × AllZero β) → ⊥)
  → (AllZero α → ⊥) ⊎ (AllZero β → ⊥)

-- Interleaving: il f g sends even index 2n to f n and odd index 2n+1 to g n.

il : El F → El F → El F
il f g zero          = f zero
il f g (suc zero)    = g zero
il f g (suc (suc n)) = il (λ m → f (suc m)) (λ m → g (suc m)) n

dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

ilEven : (f g : El F) (n : ℕ) → il f g (dbl n) ≡ f n
ilEven f g zero    = refl
ilEven f g (suc n) = ilEven (λ m → f (suc m)) (λ m → g (suc m)) n

ilOdd : (f g : El F) (n : ℕ) → il f g (suc (dbl n)) ≡ g n
ilOdd f g zero    = refl
ilOdd f g (suc n) = ilOdd (λ m → f (suc m)) (λ m → g (suc m)) n

parity : (m : ℕ) → (Σ ℕ λ n → m ≡ dbl n) ⊎ (Σ ℕ λ n → m ≡ suc (dbl n))
parity zero = inl' (zero , refl)
parity (suc m) with parity m
... | inl' (n , p) = inr' (n , cong suc p)
... | inr' (n , p) = inl' (suc n , cong suc p)

-- The three streams.  x̂ is constantly zero, ŷ interleaves α with zeros,
-- ẑ interleaves α with β.

x̂ : El F
x̂ _ = zero

ŷ : El F → El F
ŷ α = il α x̂

ẑ : El F → El F → El F
ẑ α β = il α β

-- Eq F x̂ (ẑ α β) implies both AllZero α and AllZero β.

eqXZ→A×B : (α β : El F) → Eq F x̂ (ẑ α β) → AllZero α × AllZero β
eqXZ→A×B α β h =
    (λ n → pathToEq nat' (α n) zero
             (sym (eqToPathℕ zero (ẑ α β (dbl n)) (h (dbl n))
                   ∙ ilEven α β n)))
  , (λ n → pathToEq nat' (β n) zero
             (sym (eqToPathℕ zero (ẑ α β (suc (dbl n))) (h (suc (dbl n)))
                   ∙ ilOdd α β n)))

-- AllZero α implies Eq F x̂ (ŷ α).

A→eqXY : (α : El F) → AllZero α → Eq F x̂ (ŷ α)
A→eqXY α aα m with parity m
... | inl' (n , p) =
  pathToEq nat' zero (ŷ α m)
    (sym (cong (ŷ α) p ∙ ilEven α x̂ n ∙ eqToPathℕ (α n) zero (aα n)))
... | inr' (n , p) =
  pathToEq nat' zero (ŷ α m)
    (sym (cong (ŷ α) p ∙ ilOdd α x̂ n))

-- AllZero β implies Eq F (ŷ α) (ẑ α β).

B→eqYZ : (α β : El F) → AllZero β → Eq F (ŷ α) (ẑ α β)
B→eqYZ α β aβ m with parity m
... | inl' (n , p) =
  pathToEq nat' (ŷ α m) (ẑ α β m)
    (cong (ŷ α) p ∙ ilEven α x̂ n ∙ sym (ilEven α β n) ∙ cong (ẑ α β) (sym p))
... | inr' (n , p) =
  pathToEq nat' (ŷ α m) (ẑ α β m)
    (cong (ŷ α) p ∙ ilOdd α x̂ n ∙ sym (eqToPathℕ (β n) zero (aβ n))
      ∙ sym (ilOdd α β n) ∙ cong (ẑ α β) (sym p))

-- The wrapper's co-identity is denial inequality of the base.

coEqS : (u v : El F) → (Eq F u v → ⊥) → CoEq S (u , tt) (v , tt)
coEqS u v ne e = ne e

coEqS⁻ : (u v : El F) → CoEq S (u , tt) (v , tt) → Eq F u v → ⊥
coEqS⁻ u v co e = co e

-- The wrapper is canonically equivalent to F as a carrier.

wrapperEquiv : El S ≃ El F
wrapperEquiv = Σ-contractSnd (λ _ → isContrUnit)

-- Proof-relevant presentation invariance is refuted outright: the wrapper's
-- relation is a proposition, while CoEq at the function code is not
-- (coEqPiNotProp), so no equivalence of evidence types can exist.

const1 : El F
const1 _ = suc zero

coEqSIsProp : (u v : El F) → isProp (CoEq S (u , tt) (v , tt))
coEqSIsProp u v = isPropΠ λ _ → Empty.isProp⊥

wrapperNotProofInvariant :
  (CoEq S (x̂ , tt) (const1 , tt) ≃ CoEq F x̂ const1) → ⊥
wrapperNotProofInvariant e =
  coEqPiNotProp (isOfHLevelRespectEquiv 1 e (coEqSIsProp x̂ const1))

-- Cotransitivity at the single wrapper code S yields MP∨.

mpDisjFromCotransS : Cotrans S → MPdisj
mpDisjFromCotransS ct α β ¬both =
  Sum.map
    (λ coxy → λ aα → coEqS⁻ x̂ (ŷ α) coxy (A→eqXY α aα))
    (λ coyz → λ aβ → coEqS⁻ (ŷ α) (ẑ α β) coyz (B→eqYZ α β aβ))
    (ct (x̂ , tt) (ẑ α β , tt) (ŷ α , tt)
        (coEqS x̂ (ẑ α β) (λ h → ¬both (eqXZ→A×B α β h))))
