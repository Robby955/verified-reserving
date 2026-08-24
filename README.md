# verified-reserving

Machine-checked claims reserving in Lean 4. The first target is Mack's distribution-free chain-ladder model (Mack, ASTIN Bulletin 1993), the standard method behind reserve-uncertainty calculations in property and casualty insurance.

[Blueprint](https://robby955.github.io/verified-reserving/blueprint/) (statements, dependency graph, what is proved) | [API docs](https://robby955.github.io/verified-reserving/docs/) | [Roadmap](ROADMAP.md) | [Contributing](CONTRIBUTING.md)

## What is proved

Everything below is in the repository, builds against mathlib, contains no `sorry`, and depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); CI checks all three on every push.

Deterministic layer (`VerifiedReserving/ChainLadder.lean`). A run-off triangle is a function `C : ℕ → ℕ → ℝ`. The chain-ladder development factor, the individual factors, Mack's variance estimator, the projected ultimate, the reserve, and Mack's mean squared error of prediction (MSEP) are definitions. Proved: the development factor is the weighted mean of the individual factors; the weighted sum-of-squares decomposition that gives the `n-k-2` degrees of freedom of the variance estimator; the projection identities.

Mack 1999 equals Mack 1993 (`VerifiedReserving/Recursion.lean`). Mack's 1999 paper restates the 1993 MSEP as a recursion along each accident year and says the recursion leads to the closed form. `se2rec_eq_msep` proves the two are the same estimator (for the unit-weight, `α = 1` case) whenever the development factors along the row are nonzero.

Stochastic layer (`VerifiedReserving/Stochastic.lean`). A `RandomTriangle` carries random cumulative claims and the filtration `D k` of everything observed up to development year `k`. Assumption (M1), `E[C_{i,k+1} | D_k] = f_k C_{i,k}`, is a definition. `condExp_fhatRv` proves the first part of Mack's Theorem 2: the chain-ladder factor is conditionally unbiased, `E[f̂_k | D_k] = f_k`, on the event `S_k ≠ 0`.

Twelve theorems as of 2026-08-24. The remaining stochastic layer (independence across accident years, uncorrelated factors, unbiasedness of the variance estimator, the MSEP theorem) is listed in [ROADMAP.md](ROADMAP.md) in build order; each entry names the mathlib tools it needs and is a self-contained contribution.

## Why

Mack's formula is quoted from secondary sources, circulates in several typographic variants (Mack 1993 closed form, Mack 1999 recursion, Murphy 1994 and Buchwalder-Bühlmann-Merz-Wüthrich 2006 with extra cross terms, Röhr 2016 linearized form), and two widely used implementations disagree on it (R `ChainLadder` versus `chainladder-python`, issue #234 there). A machine-checked development settles which variants are equal, records exactly which assumption each line consumes, and separates the last-period variance extrapolation, a convention, from the theorems.

## Related work

To our knowledge this is the first formalization of Mack's model, or of any claims-reserving method, in a proof assistant. Formalized actuarial mathematics does exist and this project builds beside it: Yosuke Ito's `Actuarial_Mathematics` in the Isabelle Archive of Formal Proofs and his `coq-actuary` package (interest theory, survival models, life tables, life reserves); Bjørn Kjos-Hanssen's `actlib` in Lean 4 (Cramér-Lundberg ruin, compound Poisson, interest theory, extreme value distributions); Raphael Coelho's `formal-mathfin` in Lean 4 (mathematical finance with an actuarial section). None covers chain ladder, development factors, or reserve prediction error. Corrections welcome: open an issue with a pointer.

## Build

Toolchain `leanprover/lean4:v4.32.2`, mathlib `v4.32.2`.

```
lake exe cache get
lake build
lake env lean VerifiedReserving/Test/Axioms.lean
```

Docs and blueprint locally (needs `pip install leanblueprint` and a TeX distribution):

```
lake -Kenv=dev exe cache get
lake -Kenv=dev build VerifiedReserving:docs
leanblueprint pdf
leanblueprint web
```

## Reference computation

Mack's 1993 example (the Taylor and Ashe 1983 triangle) is reproduced to every printed digit by a dependency-free Python script kept with the paper's evidence tree; it will move into `scripts/` here. The Lean definitions are over `ℝ` and noncomputable; the script is the reference computation, not the Lean code.

## Citation

See [CITATION.cff](CITATION.cff). License: Apache 2.0.
