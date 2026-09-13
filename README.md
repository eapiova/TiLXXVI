# TiLXXVI: Strong Inequality in Observational Type Theory

Agda artifact accompanying the extended abstract *Strong Inequality in
Observational Type Theory* (Trends in Logic XXVI, Sendai, November 2026) by
Riccardo Borsetto, based on an idea by Iosif Petrakis.

The construction applies the Köpp–Petrakis strong-negation recipe
(*Strong negation in the theory of computable functionals TCF*, LMCS
21(2:1), 2025) to the clauses of observational equality over a small
Tarski universe, yielding a strong inequality defined by the same
recursion that defines equality.

## Contents

- `HObsTT/` — the closed set-level model: the five-constructor universe
  (`Universe`), observational equality and its dual (`Eq`, `CoEq`), and
  the theorems of the abstract: incompatibility, symmetry, proof
  relevance, calibrated cotransitivity with the disjunctive-Markov bound
  (`Cotransitivity`), global tightness (`Tightness`), relation-level
  involution (`Involutivity`), eliminator-free restricted ex falso
  (`EfQ`), and the derived polarized connectives (`Polarization`).
- `BHObsTT/` — the strong-map layer: functions packaged with a
  co-action on strong inequality, identities and composition, strong
  structure for the derived connectives (`StrongMap`,
  `StrongConnectives`).

A separate syntactic development (reified formulas, signed atoms, and
the Chu/antithesis comparisons mentioned in the abstract) is part of a
larger repository, available from the author on request.

## Checking

Requires Agda 2.9.0 and the [cubical library](https://github.com/agda/cubical) 0.9.

```
agda Everything.agda
```

Every module uses `--cubical --safe`; there are no postulates and no
unfinished obligations.
