# Verified Reserving

[![CI](https://github.com/Robby955/verified-reserving/actions/workflows/ci.yml/badge.svg)](https://github.com/Robby955/verified-reserving/actions/workflows/ci.yml)
[![Blueprint](https://github.com/Robby955/verified-reserving/actions/workflows/blueprint.yml/badge.svg)](https://github.com/Robby955/verified-reserving/actions/workflows/blueprint.yml)
[![Release](https://img.shields.io/github/v/release/Robby955/verified-reserving?label=release)](https://github.com/Robby955/verified-reserving/releases/latest)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.2-blue)](https://leanprover.github.io/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

**Machine-checked mathematics for claims reserving and actuarial risk in Lean 4.**

The library formalizes results from Mack chain ladder, Munich chain ladder, over-dispersed Poisson models, one-year claims development, Bornhuetter-Ferguson prediction error, Bühlmann-Straub credibility, and Panjer recursion. The Lean statements expose their formal hypotheses; the statement-fidelity ledger records source alignment and gaps. The repository distinguishes proved theorems from encoded estimators, approximations, and actuarial conventions.

[Blueprint](https://robby955.github.io/verified-reserving/blueprint/) · [API documentation](https://robby955.github.io/verified-reserving/docs/) · [Theorem catalogue](docs/THEOREM_CATALOGUE.md) · [Statement fidelity](docs/STATEMENT_FIDELITY.md) · [Latest release](https://github.com/Robby955/verified-reserving/releases/latest)

## Mathematical core

For a cumulative run-off triangle $C_{i,k}$, the chain-ladder factor is

```math
\widehat f_k
=
\frac{\displaystyle\sum_{i=0}^{n-k-2} C_{i,k+1}}
     {\displaystyle\sum_{i=0}^{n-k-2} C_{i,k}}.
```

When each contributing $C_{i,k}$ is nonzero, Lean proves that $\widehat f_k$ is the $C_{i,k}$-weighted mean of the individual factors $F_{i,k}=C_{i,k+1}/C_{i,k}$ in [`fhat_eq_weighted_average`](VerifiedReserving/ChainLadder.lean).

For a $\mathcal D$-measurable predictor $P$ and target $Y$, under the stated measurability and integrability hypotheses, the exact conditional prediction-error identity holds almost surely:

```math
\mathbb E\!\left[(P-Y)^2\mid\mathcal D\right]
=
\mathrm{Var}(Y\mid\mathcal D)
+
\left(P-\mathbb E[Y\mid\mathcal D]\right)^2.
```

Lean proves this as [`condExp_sq_sub_of_stronglyMeasurable`](VerifiedReserving/Msep.lean). [`condMsep_eq`](VerifiedReserving/Msep.lean) specializes it under Mack's conditional moment assumptions plus explicit observed-data, measurability, and integrability hypotheses; [`condMsep_eq_of_rows`](VerifiedReserving/ObservedData.lean) derives these conditions from row-conditioned Mack assumptions, a row-generated filtration, and independent accident years.

Write $S_k=\sum_{r=0}^{n-k-2}C_{r,k}$ for the observed column total, $\widehat C_{i,k}$ for the chain-ladder projection, and $\widehat\sigma_k^2$ for Mack's variance estimator. The familiar plug-in expression is kept separate as a definition:

```math
\widehat{\mathrm{msep}}_i
=
\widehat C_{i,n-1}^{\,2}
\sum_{k=n-1-i}^{n-2}
\frac{\widehat\sigma_k^{\,2}}{\widehat f_k^{\,2}}
\left(
  \frac{1}{\widehat C_{i,k}}
  +
  \frac{1}{S_k}
\right).
```

This separation prevents an exact conditional theorem from being confused with its data-based estimator.

## Formalized scope

| Area | Representative results |
|---|---|
| Mack chain ladder | [Conditional MSEP](VerifiedReserving/Msep.lean), [total MSEP](VerifiedReserving/TotalMsep.lean), process and estimation variance, factor moments, and [$\widehat\sigma_k^2$ unbiasedness](VerifiedReserving/SigmaUnbiased.lean). |
| Reserving variants | [Weighted Mack 1999](VerifiedReserving/Mack1999.lean), the [represented Röhr formula](VerifiedReserving/Rohr.lean), [arbitrary-horizon definitions](VerifiedReserving/RohrHorizon.lean), and both branches of source-pinned R [`ChainLadder` 0.2.22](VerifiedReserving/ChainLadderR.lean). |
| Paid and incurred | The [Quarg-Mack separate-projection gap](VerifiedReserving/MunichChainLadder.lean), [residual-regression identities](VerifiedReserving/MunichStochastic.lean), and reduction of the coupled Munich projection at zero slopes. |
| One-year risk | [Development-year](VerifiedReserving/CDR.lean) and [calendar-year](VerifiedReserving/CDRCalendar.lean) true CDR moments, finite witnesses, and the [Merz-Wüthrich product-to-sum remainder](VerifiedReserving/CDRMsep.lean). |
| ODP | [Chain-ladder score equations](VerifiedReserving/ODP.lean), [stochastic cell moments and prediction error](VerifiedReserving/ODPStochastic.lean), and definition-level delta-method and bootstrap formulas. |
| Credibility and BF | [Bühlmann-Straub prediction risk](VerifiedReserving/BuhlmannStraubStochastic.lean) and credibility minimization; [Mack 2008 Bornhuetter-Ferguson](VerifiedReserving/BFPredictionError.lean) mean, variance, prediction error, and raw estimators. |
| Aggregate loss | [Panjer's recursion](VerifiedReserving/Panjer.lean) as a formal-series identity; probability normalization and nonnegativity remain assumptions. |

The [theorem catalogue](docs/THEOREM_CATALOGUE.md) maps the source statements to Lean names and proof status. The [blueprint](https://robby955.github.io/verified-reserving/blueprint/) provides the dependency graph and a typeset account of the development.

## Verification and boundaries

- The full library builds against mathlib without `sorry` or custom axioms.
- CI audits the proof dependencies of 479 named declarations. Each audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms.
- Finite nondegenerate stochastic models instantiate representative assumptions and wrapper theorems.
- [`docs/STATEMENT_FIDELITY.md`](docs/STATEMENT_FIDELITY.md) records the hypotheses and source differences for headline results.
- Delta-method formulas, bootstrap procedures, tail choices, and final-period variance extrapolation are marked as definitions or conventions. Their statistical validity is not asserted as a Lean theorem.
- The scripts reproduce published examples and package outputs numerically; numerical agreement is evidence for the transcription, not a formal proof.

## Build

Toolchain: `leanprover/lean4:v4.32.2`, mathlib `v4.32.2`.

```bash
lake exe cache get
lake build
lake env lean VerifiedReserving/Test/Axioms.lean
```

Reference computations and their pinned Python dependencies are documented in [`scripts/README.md`](scripts/README.md).

## Documentation and citation

- [Typeset blueprint](https://robby955.github.io/verified-reserving/blueprint/)
- [Generated API documentation](https://robby955.github.io/verified-reserving/docs/)
- [Statement-fidelity ledger](docs/STATEMENT_FIDELITY.md)
- [Roadmap and explicit open boundaries](ROADMAP.md)
- [Contributing](CONTRIBUTING.md)
- [Release v0.2.0](https://github.com/Robby955/verified-reserving/releases/tag/v0.2.0)

Citation metadata is in [`CITATION.cff`](CITATION.cff). The code is available under the [Apache 2.0 license](LICENSE).
