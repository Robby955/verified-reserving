# Changelog

## v0.2.0 - 2026-08-25

- 479 axiom-audited Lean declarations, 214 more than v0.1.0, with no proof gaps.
- Munich paid/incurred gap and residual-regression results, including reduction to separate chain ladder at zero residual slopes.
- Stochastic ODP moments, exact process-plus-estimation identities, delta-method and bootstrap definitions, and a finite independent-cell witness.
- Mack 1999 row-conditioned weighted assumptions, active-contributor variance estimation, and finite witnesses for `α = 0` and `α = 2`.
- Calendar-year CDR conditioning, exact true-CDR moments, the Merz-Wüthrich product-to-sum remainder, and finite witness instances.
- Röhr arbitrary-horizon definitions and algebraic bounds, plus formula-level semantics for both R `ChainLadder` 0.2.22 `mse.method` branches.
- Stochastic Bühlmann-Straub prediction risk, Mack 2008 Bornhuetter-Ferguson prediction error, and Panjer's compound-distribution recursion.
- Updated blueprint and statement-fidelity ledger, preserving the distinction between theorems, estimators, approximations, and conventions.

## v0.1.0 - 2026-08-25

First versioned research release.

- 265 audited Lean declarations covering Mack's chain-ladder model, exact conditional MSEP results, the total-reserve form, independence across accident years, and selected reserving variants.
- A statement-fidelity ledger separating source statements, Lean hypotheses, estimators, approximations, and conventions.
- Kernel-checked arithmetic for Mack's Taylor-Ashe example and finite witnesses for (M1), (M3), (M2') and accident-year independence.
- Reference computations for the Taylor-Ashe and RAA triangles plus a theorem-aware screen of 779 Schedule P triangles, with 638 audited and 141 classified as degenerate.
- A Lean blueprint, generated API documentation, pinned scientific-Python dependencies, and reproducible release checks.
