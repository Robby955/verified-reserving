# verified-reserving

Machine-checked claims reserving in Lean 4: Mack's distribution-free chain-ladder model.

Status (2026-08-24): 12 theorems, 0 sorry, axioms = propext, Classical.choice, Quot.sound. Deterministic layer complete for the 1993 estimators; Mack 1999 recursion proved equal to the 1993 closed form; first stochastic theorem (Mack 1993 Theorem 2, conditional unbiasedness of the development factor under assumption (M1)) proved. Remaining stochastic layer in ROADMAP.md.

## Layout

- `VerifiedReserving/ChainLadder.lean`: run-off triangle as `ℕ → ℕ → ℝ`; column sums `S`, `T`; development factor `fhat`; individual factors `F`; Mack's `sigma2`; projection `Chat`; `ultimate`, `reserve`; Mack's `msep` (1993, Theorem 3). Proved: `fhat` is the `C`-weighted mean of individual factors; the weighted sum-of-squares decomposition around any centre and its collapse at `fhat`; the one-step projection identity; the oldest year has zero reserve.
- `VerifiedReserving/Recursion.lean`: Mack's 1999 recursive standard error `se2rec` (α = 1, unit weights); `se2rec_eq_msep` proves it equals the 1993 `msep` whenever the development factors along the row are nonzero.
- `VerifiedReserving/Stochastic.lean`: `RandomTriangle` (random cumulative claims plus the filtration `D k` of development years `0..k`); `Mack1` = assumption (M1) in the `D_k`-conditioned form `E[C_{i,k+1} | D_k] = f_k C_{i,k}`; `condExp_fhatRv` proves `E[f̂_k | D_k] = f_k` on `{S_k ≠ 0}` (Mack 1993, Theorem 2, first part) via mathlib's conditional expectation.
- `VerifiedReserving/Test/Axioms.lean`: `#print axioms` for every theorem.
- `scripts/trim_manifest.py`: keeps the lake manifest to mathlib and its dependencies.

## Build

Toolchain `leanprover/lean4:v4.32.2`, mathlib `v4.32.2` (see `lake-manifest.json`). The `.lake/packages` directory was cloned (APFS copy-on-write) from an already-built mathlib checkout; a fresh clone should run `lake exe cache get` instead.

```
lake build
lake env lean VerifiedReserving/Test/Axioms.lean
```

## Reference computation

`experiments/variance-mack-2027/reproduce_mack1993.py` in the research-ops tree recomputes Mack (1993) Tables 2 and 3 from the Taylor and Ashe (1983) triangle; all printed values are reproduced.
