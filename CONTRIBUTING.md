# Contributing

Contributions are welcome, from a one-line lemma to a whole theorem of the roadmap.

## Where to start

- [ROADMAP.md](ROADMAP.md) lists the open theorems in build order with the mathlib tools each needs. Pick one, open an issue with the "Theorem proposal" template saying you are on it, and go.
- The [blueprint](https://robby955.github.io/verified-reserving/blueprint/) shows every statement and its dependency graph; nodes not yet green are the open work.

## Good first theorems

Each of these is self-contained, cites a specific source, and reuses lemmas already in the repository.

1. Mack (1999), general weights and exponent. The factor estimator with weights `w_{ik}` and exponent `α` on `C_{ik}` (`α = 1`, unit weights is the 1993 estimator). Prove the weighted-average form and, under (M1), conditional unbiasedness; then the recursion identity `se2rec_eq_msep` for general `α`. Deterministic part first (`ChainLadder.lean` style), stochastic part after (`Stochastic.lean` style).
2. Bornhuetter-Ferguson with prior uncertainty. `BornhuetterFerguson.lean` has the deterministic identities; add a random a priori ultimate independent of the triangle and prove the conditional mean and variance of the BF reserve (Mack 2008, "The prediction error of Bornhuetter-Ferguson", ASTIN Bulletin 38).
3. Bühlmann-Straub credibility. The credibility estimator as the minimizer of a weighted quadratic loss: the normal equations follow the pattern of `weighted_sq_dev_at_fhat`.
4. A witness for the independence layer: a concrete `RandomTriangle` on a finite probability space satisfying `RowsIndep` and `RowsGenerateD` (see `Test/NontrivialModel.lean` for the style), instantiating `mack1_of_mack1Row`.
5. Catalogue rows: any published form of the prediction-error formula not yet in `Catalogue.lean` or `Rohr.lean`, proved equal to Mack's or separated from it by an explicit term with a counterexample triangle.
6. Deterministic identities and docstrings: the projection and weighted-sum lemmas in `ChainLadder.lean` are the entry point for anyone new to Lean.

## Rules

1. No `sorry`, no `admit`, no custom `axiom`. CI rejects them.
2. Every new theorem goes into `VerifiedReserving/Test/Axioms.lean` as a `#print axioms` line so the audit covers it. CI fails on any axiom outside `propext`, `Classical.choice`, `Quot.sound`, and CI's audited-theorem threshold in `.github/workflows/ci.yml` goes up with your count.
3. State theorems the way the source states them. When a paper's formula is an approximation (Mack's estimation-error step, for example), the Lean statement says so in the docstring and the blueprint says so in the text; do not upgrade an estimator to an identity. Conventions the source leaves open (the last-period variance parameter, division by a vanishing quantity) are definitions that no theorem consumes.
4. Cite the source for each statement in the docstring: paper, year, theorem or equation number.
5. Add the statement to the blueprint (`blueprint/src/content.tex`, or a new `blueprint/src/<module>.tex` that `content.tex` inputs) with `\lean{}` and `\leanok` when proved, and its name to `blueprint/lean_decls`; `lake -Kenv=dev exe checkdecls blueprint/lean_decls` must pass.
6. Keep the deterministic and stochastic layers separate: anything provable without a probability space belongs in the deterministic files.
7. New hypotheses go into new definitions with a docstring saying what supplies them in the source (independence across accident years, integrability, nonvanishing column sums); existing theorem statements do not change.

## Workflow

```
lake exe cache get
lake build
lake env lean VerifiedReserving/Test/Axioms.lean
lake env lean VerifiedReserving/Test/Witness.lean
lake -Kenv=dev exe checkdecls blueprint/lean_decls
```

Working on several theorems at once: give each its own worktree on its own branch and share the prebuilt mathlib,

```
git worktree add ../vr-<topic> -b feat/<topic> main
cd ../vr-<topic> && mkdir -p .lake && ln -s "$(git rev-parse --show-toplevel)/../verified-reserving/.lake/packages" .lake/packages && lake build
```

Open a pull request against `main`. CI runs the build, the sorry and axiom checks, the axiom audit and the non-vacuity witness.

## Scope

Mack's model first, then the neighbours that practising actuaries use with it: the Merz-Wüthrich one-year uncertainty, Bornhuetter-Ferguson, Panjer's recursion for compound distributions, Bühlmann-Straub credibility. Life contingencies are covered elsewhere (see the related work in the README); we do not duplicate them.
