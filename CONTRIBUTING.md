# Contributing

Contributions are welcome, from a one-line lemma to a whole theorem of the roadmap.

## Where to start

- [ROADMAP.md](ROADMAP.md) lists the open theorems in build order with the mathlib tools each needs. Pick one, open an issue saying you are on it, and go.
- The [blueprint](https://robby955.github.io/verified-reserving/blueprint/) shows every statement and its dependency graph; nodes not yet green are the open work.
- Good first contributions: catalogue rows (prove two published forms of the MSEP formula equal, or exhibit a counterexample triangle), extra deterministic identities, docstrings.

## Rules

1. No `sorry`, no `admit`, no custom `axiom`. CI rejects them.
2. Every new theorem goes into `VerifiedReserving/Test/Axioms.lean` so the axiom audit covers it. CI fails on any axiom outside `propext`, `Classical.choice`, `Quot.sound`.
3. State theorems the way the source states them. When a paper's formula is an approximation (Mack's estimation-error step, for example), the Lean statement says so in the docstring and the blueprint says so in the text; do not upgrade an estimator to an identity.
4. Cite the source for each statement in the docstring: paper, year, theorem or equation number.
5. Add the statement to `blueprint/src/content.tex` with `\lean{}` and `\leanok` when proved, and its name to `blueprint/lean_decls`.
6. Keep the deterministic and stochastic layers separate: anything provable without a probability space belongs in the deterministic files.

## Workflow

```
lake exe cache get
lake build
lake env lean VerifiedReserving/Test/Axioms.lean
```

Open a pull request against `main`. CI runs the build, the sorry/axiom checks, and the axiom audit.

## Scope

Mack's model first, then the neighbours that practising actuaries use with it: the Merz-Wüthrich one-year uncertainty, Bornhuetter-Ferguson, Panjer's recursion for compound distributions, Bühlmann-Straub credibility. Life contingencies are covered elsewhere (see the related work in the README); we do not duplicate them.
