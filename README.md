# verified-reserving

Machine-checked claims reserving in Lean 4: Mack's distribution-free chain-ladder model.

Status (2026-08-23): deterministic layer built and axiom-audited (7 theorems, 0 sorry, axioms = propext, Classical.choice, Quot.sound). Stochastic layer (Mack's three assumptions, unbiasedness, MSEP theorem) not yet started; see ROADMAP.md.

## Layout

- `VerifiedReserving/ChainLadder.lean`: run-off triangle as `ℕ → ℕ → ℝ`; column sums `S`, `T`; development factor `fhat`; individual factors `F`; Mack's `sigma2`; projection `Chat`; `ultimate`, `reserve`; Mack's `msep` (1993, Theorem 3). Proved: `fhat` is the `C`-weighted mean of individual factors; the weighted sum-of-squares decomposition around any centre and its collapse at `fhat`; the one-step projection identity; the oldest year has zero reserve.
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
