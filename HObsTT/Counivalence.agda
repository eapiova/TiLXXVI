{-# OPTIONS --cubical --safe #-}

module HObsTT.Counivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (inl to inl'; inr to inr')
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.Incompatibility

EqU : U → U → Type₀
EqU A B =
  Σ (El A → El B) λ f →
  Σ (El B → El A) λ g →
  ((x : El A) → Eq A x (g (f x)))
  × ((y : El B) → Eq B y (f (g y)))

CoEqU : U → U → Type₀
CoEqU A B =
  (f : El A → El B) → (g : El B → El A) →
  (Σ (El A) (λ x → CoEq A x (g (f x))))
  ⊎ (Σ (El B) (λ y → CoEq B y (f (g y))))

incompU : (A B : U) → CoEqU A B → EqU A B → ⊥
incompU A B co (f , g , sec , ret) with co f g
... | inl' (x , co-x) = incomp A x (g (f x)) co-x (sec x)
... | inr' (y , co-y) = incomp B y (f (g y)) co-y (ret y)

strengthU : (A B : U) → CoEqU A B → El A ≃ El B → ⊥
strengthU A B co e = incompU A B co (equivFun e , invEq e , sec , ret)
  where
    sec : (x : El A) → Eq A x (invEq e (equivFun e x))
    sec x = pathToEq A x (invEq e (equivFun e x)) (sym (retEq e x))

    ret : (y : El B) → Eq B y (equivFun e (invEq e y))
    ret y = pathToEq B y (equivFun e (invEq e y)) (sym (secEq e y))

strengthU-path : (A B : U) → CoEqU A B → A ≡ B → ⊥
strengthU-path A B co p = strengthU A B co (pathToEquiv (cong El p))

coEqU-example : CoEqU nat' bot'
coEqU-example f g = ⊥-rec (f zero)
