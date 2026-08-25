---
name: Theorem proposal
about: Propose a statement to formalize, or claim one from the roadmap
title: "[theorem] "
labels: theorem
---

**Statement (in words, then the formula).** What is to be proved, with the source: paper, year, theorem or equation number.

**Hypotheses.** Which of (M1), (M2), (M3) it uses, in which form (row-conditioned or `D_k`-conditioned), plus integrability or nonvanishing conditions.

**Status in the source.** Exact theorem, estimator (definition), approximation, or convention. If the source calls it an approximation, the Lean statement must say so.

**Where it goes.** Existing module or a new one; deterministic layer or stochastic layer.

**mathlib tools.** The lemmas you expect to need (`condExp_*`, `iIndep*`, `Finset.*`), if known.

**Blueprint node.** The `\uses{}` it depends on.
