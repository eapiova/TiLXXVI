{-# OPTIONS --cubical --safe #-}

-- Aggregator for the HObsTT base layer:
-- Tarski universe + observational equality/co-equality + their key
-- properties (incompatibility, apartness, unique choice, involutivity, EFQ,
-- and the universe-level EqU/CoEqU).

module HObsTT.Everything where

open import HObsTT.Universe
open import HObsTT.Eq
open import HObsTT.CoEq
open import HObsTT.Incompatibility
open import HObsTT.Apartness
open import HObsTT.AUC
open import HObsTT.Involutivity
open import HObsTT.Counivalence
open import HObsTT.EfQ
open import HObsTT.Cotransitivity
open import HObsTT.Polarization
open import HObsTT.Tightness
