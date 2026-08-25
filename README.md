# verified-reserving

Machine-checked claims reserving in Lean 4. The first target is Mack's distribution-free chain-ladder model (Mack, ASTIN Bulletin 1993), the standard method behind reserve-uncertainty calculations in property and casualty insurance.

[Blueprint](https://robby955.github.io/verified-reserving/blueprint/) (statements, dependency graph, what is proved) | [API docs](https://robby955.github.io/verified-reserving/docs/) | [Roadmap](ROADMAP.md) | [Contributing](CONTRIBUTING.md)

## What is proved

Everything below is in the repository, builds against mathlib, contains no `sorry`, and depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); CI checks all three on every push.

Deterministic layer (`VerifiedReserving/ChainLadder.lean`). A run-off triangle is a function `C : ℕ → ℕ → ℝ`. The chain-ladder development factor, the individual factors, Mack's variance estimator, the projected ultimate, the reserve, and Mack's mean squared error of prediction (MSEP) are definitions. Proved: the development factor is the weighted mean of the individual factors; the weighted sum-of-squares decomposition that gives the `n-k-2` degrees of freedom of the variance estimator; the projection identities.

Mack 1999 equals Mack 1993 (`VerifiedReserving/Recursion.lean`). Mack's 1999 paper restates the 1993 MSEP as a recursion along each accident year and says the recursion leads to the closed form. `se2rec_eq_msep` proves the two are the same estimator (for the unit-weight, `α = 1` case) whenever the development factors along the row are nonzero.

Bornhuetter-Ferguson (`VerifiedReserving/BornhuetterFerguson.lean`). The BF reserve and ultimate on the chain-ladder pattern as definitions; proved: linearity in the a priori ultimate, BF with the chain-ladder ultimate as prior returns chain ladder exactly, and the BF reserve is a fraction of the prior when every development factor is at least one.

Stochastic layer (`VerifiedReserving/Stochastic.lean`). A `RandomTriangle` carries random cumulative claims and the filtration `D k` of everything observed up to development year `k`. Assumption (M1), `E[C_{i,k+1} | D_k] = f_k C_{i,k}`, is a definition. Mack's Theorem 2 is proved in full: `condExp_fhatRv` gives `E[f̂_k | D_k] = f_k` on `{S_k ≠ 0}`, `condExp_fhatRv_mul` gives `E[f̂_j f̂_k | D_j] = f_j f_k` for `j < k` by the tower property, and `integral_fhatRv`, `integral_fhatRv_mul` are the unconditional forms: the chain-ladder factors are unbiased and uncorrelated.

Mack's Theorem 1 (`VerifiedReserving/Ultimate.lean`). `condExp_C_of_Mack1` iterates (M1) to `E[C_{i,d+m} | D_d] = C_{i,d} ∏ f_k`; `condExp_ChatRv` shows the chain-ladder projection has the same conditional expectation; `condExp_ultimate_eq` is the statement actuaries quote: the chain-ladder ultimate is a conditionally unbiased estimator of the true ultimate claims, `E[Ĉ_{i,n-1} | D_d] = E[C_{i,n-1} | D_d]`.

Estimation variance (`VerifiedReserving/Variance.lean`). Assumptions (M3) (conditional variance) and (M2') (conditional uncorrelatedness of residuals across accident years) as definitions; `condExp_sq_fhatRv_sub` proves E[(f̂_k − f_k)² | D_k] = σ²_k / S_k, the estimation-variance term of Mack's formula.

Unbiasedness of σ̂² (`VerifiedReserving/SigmaUnbiased.lean`). `weighted_sq_dev_eps` rewrites the weighted sum of squares around f̂_k as residual terms minus S_k(f̂_k − f_k)²; `condExp_sigma2Rv` then gives E[σ̂²_k | D_k] = σ²_k for k + 3 ≤ n, which is exactly why Mack divides by n − k − 2.

Process variance and Theorem 3 (`VerifiedReserving/ProcessVariance.lean`, `VerifiedReserving/Msep.lean`). Conditional second moments and their tower recursion; `procVar`, the process variance along a row, proved equal to the conditional variance of the true claims; the exact conditional-MSEP decomposition for any measurable predictor; and `condMsep_eq`, Mack's Theorem 3 in exact form conditioned on the observed data: process variance plus squared estimation error. Mack's plug-in estimators of the two terms, including the conditional-resampling approximation, are definitions (`mackProcess`, `mackEstimation`), so the exact statement and the approximation never get confused.

The variant catalogue (`VerifiedReserving/Catalogue.lean`). With `a_k = σ̂²_k/(f̂²_k S_k)`, Mack's estimation-error term `Ĉ² Σ a_k` is proved to be the first-order part of the conditional-resampling term `Ĉ² (∏(1 + a_k) − 1)` of Buchwalder, Bühlmann, Merz and Wüthrich (2006): Mack ≤ BBMW, the difference is exactly `Ĉ² (∏(1+a_k) − 1 − Σ a_k)`, the two coincide when a single development factor is involved, and the difference is second order (at most `Ĉ² (e^{Σ a} − 1 − Σ a)`). That is the algebraic content of a twenty-year discussion, settled by the kernel; which estimator has better statistical properties remains a statistical question (Gisler 2019, Siegenthaler 2023).

A non-vacuity witness (`VerifiedReserving/Test/Witness.lean`, run in CI) exhibits a concrete random triangle satisfying every hypothesis of the stochastic theorems and instantiates Theorems 1 and 2 on it. Writing it caught a hypothesis that no real triangle could satisfy (a nonvanishing column sum demanded for columns with no contributors); the theorems now ask for it only where the row uses it.

Fifty-four theorems as of 2026-08-25. The remaining stochastic layer (independence across accident years as the source of the `D_k` form of (M1), assumption (M3), unbiasedness of the variance estimator, the MSEP theorem) is listed in [ROADMAP.md](ROADMAP.md) in build order; each entry names the mathlib tools it needs and is a self-contained contribution.

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
