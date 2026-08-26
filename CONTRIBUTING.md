# Contributing

Contributions are welcome, from a one-line lemma to a whole theorem of the roadmap.

## Where to start

- [ROADMAP.md](ROADMAP.md) lists current priorities, completed modules and their remaining gaps. Pick one bounded item, open an issue with the "Theorem proposal" template saying you are on it, and go.
- The [blueprint](https://robby955.github.io/verified-reserving/blueprint/) is the proved-statement catalogue and dependency graph. Open work is tracked in the roadmap rather than represented by placeholder nodes.

## Open contribution directions

The former good-first list is complete. Current work is narrower and varies in difficulty; check the matching `Still open` paragraph in [ROADMAP.md](ROADMAP.md) before starting.

R `ChainLadder` option semantics are closed in `ChainLadderR.lean` against package version 0.2.22 and source commit `41f4e949`; follow-up work should use a newer pinned source diff.

1. Add distribution-specific ODP process simulators and prove bootstrap properties only under explicit distributional assumptions.
2. Formalize an observable-CDR approximation under stated linearization or resampling hypotheses; keep it separate from the exact true-CDR results.
3. Formalize Bühlmann-Straub Section 7 structural-parameter estimators without folding them into the proved conditional-moment model; record source truncation rules as definitions unless their properties are proved.
4. Construct a positive-variance witness for the Bornhuetter-Ferguson prediction-error layer.
5. Extend the Röhr development-horizon layer only when a primary source supports the additional aggregation formulas.

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
git fetch origin
git worktree add ../vr-<topic> -b feat/<topic> origin/main
cd ../vr-<topic> && mkdir -p .lake && ln -s "$(git rev-parse --show-toplevel)/../verified-reserving/.lake/packages" .lake/packages && lake build
```

Open a pull request against `main`. CI runs the build, the sorry and axiom checks, the axiom audit and the non-vacuity witness.

## Scope

Mack's model first, then the neighbours that practising actuaries use with it: Munich chain ladder, the Merz-Wüthrich one-year uncertainty, the ODP stochastic layer, Bornhuetter-Ferguson, Bühlmann-Straub credibility and, later, Panjer's recursion for compound distributions. Life contingencies are covered elsewhere (see the related work in the README); we do not duplicate them.
