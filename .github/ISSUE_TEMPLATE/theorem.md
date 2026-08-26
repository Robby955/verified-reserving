---
name: Theorem proposal
about: Propose a statement to formalize, or claim one from the roadmap
title: "[theorem] "
labels: theorem
---

**Statement (in words, then the formula).** What is to be proved, with the source: paper, year, theorem or equation number.

**Hypotheses.** State the applicable model assumptions in their exact conditioning form, plus integrability, measurability, independence, positivity, or nonvanishing conditions.

**Status in the source.** Exact theorem, estimator (definition), approximation, or convention. If the source calls it an approximation, the Lean statement must say so.

**Where it goes.** Existing module or a new one; deterministic layer or stochastic layer.

**mathlib tools.** The lemmas you expect to need (`condExp_*`, `iIndep*`, `Finset.*`), if known.

**Blueprint node.** The `\uses{}` it depends on.
