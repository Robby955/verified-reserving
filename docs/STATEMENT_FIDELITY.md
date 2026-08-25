# Statement fidelity

What the published statement says, what the Lean declaration says, and the distance between the two.

Each entry has three parts. **Source** quotes or closely paraphrases the published statement with
its citation, giving a page or a display number where the module docstring records one. **Lean**
states the declaration in prose exactly as the Lean says it, with every hypothesis listed:
integrability, almost-sure nonvanishing of column sums, the form of the filtration, whether an
assumption is the row-conditioned or the `D_k`-conditioned one, the "no further information"
hypotheses, nonnegativity. **Gap** says plainly how far apart they are.

## Rules the development follows

1. **Estimators are definitions.** Where a paper displays an estimator, the library records a
   definition and proves identities about it. `msep`, `msepTotal`, `mackProcess`, `mackEstimation`,
   `bbmwEstimation`, `rohrMsep` and `msepW` are definitions. No theorem claims that any of them is
   unbiased for, or converges to, the quantity it estimates. The exact conditional objects
   (`condMsep_eq`, `condMsepTotal_eq`) are separate statements, so the approximation and the thing
   approximated never get confused.
2. **Conventions are consumed by no theorem.** Mack's last-period variance extrapolation and the
   1999 tail factor are conventions supplied by the actuary. `tailUltimate` and `tailSe2Step` are
   definitions that no theorem uses; the last-period rule is not in the library at all.
3. **`x / 0 = 0`.** Lean's division is total. Several identities therefore hold with no
   nonvanishing hypothesis where a paper would need a side condition (`rohrMsep_eq_msep`,
   `fhatW_eq_weighted_average`), and one definition returns `0` where the quantity is not estimable
   (`sigma2 C n (n-2) = 0`, since its divisor `n - k - 2` is zero).
4. **Three standard axioms.** Every audited declaration depends only on `propext`,
   `Classical.choice` and `Quot.sound`, or on no axiom at all.
5. **CI audit.** `VerifiedReserving/Test/Axioms.lean` runs `#print axioms` on every name in this
   document. CI rejects a nonstandard axiom, rejects any `sorry`, `admit` or `axiom` declaration,
   requires at least 265 audited lines, and runs the non-vacuity witness.

Conventions: accident years `i` and development years `k` are zero-based, `C i k` is observed when
`i + k <= n - 1`, `d = n - 1 - i` is the latest observed development year of accident year `i`, and
`S_k`, `T_k` are the two column sums over `contributors n k = range (n - k - 1)`.

## Index

| Source statement | Lean declaration | Gap |
|---|---|---|
| Mack 1993, eq. (2): `f̂_k` is the `C`-weighted mean of the `F_{i,k}` | `fhat_eq_weighted_average` | identical, with a nonvanishing hypothesis on the individual denominators only |
| Mack 1993, degrees of freedom of `σ̂²_k` | `weighted_sq_dev`, `weighted_sq_dev_at_fhat` | identical |
| Mack 1993, Theorem 1 | `condExp_ultimate_eq`, `condExp_ChatRv`, `condExp_C_of_Mack1` | Lean stronger hypotheses: integrability, a.s. nonvanishing column sums, finite measure |
| Mack 1993, Theorem 2 | `condExp_fhatRv`, `condExp_fhatRv_mul`, `integral_fhatRv`, `integral_fhatRv_mul` | Lean stronger hypotheses: integrability, a.s. nonvanishing `S_k` |
| Mack 1993, proof of Theorem 3: estimation variance of `f̂_k` | `condExp_sq_fhatRv_sub` | identical up to integrability and a.s. nonvanishing `S_k` |
| Mack 1993, proof of Theorem 3: `σ̂²_k` unbiased | `condExp_sigma2Rv`, `condExp_wssRv`, `weighted_sq_dev_eps` | Lean stronger hypotheses: `k + 3 <= n`, every contributing `C_{i,k}` a.s. nonzero |
| Mack 1993, process variance along a row | `condVar_C_eq_procVar`, `procVar`, `procVar_eq_sum` | identical |
| Mack 1993, Theorem 3, exact conditional form | `condMsep_eq`, `condExp_sq_sub_of_stronglyMeasurable`, `condMsep_eq_of_rows` | `condMsep_eq` exposes the "no further information" hypotheses; `condMsep_eq_of_rows` derives them from the row assumptions, `RowsGenerateD`, accident-year independence and square integrability |
| Mack 1993, Theorem 3, plug-in estimator | `msep`, `mackProcess`, `mackEstimation` | source statement is an estimator; Lean has it as a definition and proves identities about it |
| Mack 1993, closed form as process plus estimation | `msep_eq_mackProcess_add_mackEstimation`, `msep_eq_mackProcess_add_mackEstimation_of_lt` | identical, with nonvanishing factors and projections along the row |
| Mack 1993, Corollary (total reserve), plug-in | `msepTotal`, `mackCross`, `mackTotalEstimation` | source statement is an estimator; Lean has it as a definition |
| Mack 1993, Corollary, exact form | `condMsepTotal_eq`, `sum_procVar_le_condMsepTotal`, `condMsepTotal_eq_of_rows` | the base theorem exposes `CondCrossFree` and the per-row `hfut` hypotheses; `condMsepTotal_eq_of_rows` derives them from the row assumptions, `RowsGenerateD`, accident-year independence and square integrability |
| Mack 1993, Corollary: plug-in has the exact shape | `msepTotal_eq_sum_mackProcess_add_mackTotalEstimation` | identical, with nonvanishing factors and projections on every row |
| Mack 1993, eq. (1) and (2), pp. 214-215: (M1), (M3) row-conditioned and `D_k` forms | `Mack1Row`, `Mack3Row`, `Mack1`, `Mack3`, `mack1_of_mack1Row`, `mack3_of_mack3Row` | Lean stronger hypotheses: `RowsGenerateD`, integrability; the source's one-sentence passage is proved |
| The general fact behind the passage | `condExp_sup_of_indep`, `setIntegral_inter_of_indep` | not in the source; mathlib has only the case `m₁ = ⊥` |
| (M2'), the cross-term condition | `Mack2'`, `mack2'_of_rows` | Lean derives what the source leaves implicit, from (M2) and (M1row) |
| Mack 1999, recursion equals the 1993 closed form (`α = 1`, unit weights) | `se2rec_eq_msep`, `se2rec_eq_closed` | Lean stronger hypothesis: nonzero development factors along the row |
| Mack 1999, eq. (*) and the recursion below it, general `w` and `α` | `msepW`, `se2recW`, `se2recW_eq_msepW`, `msepW_unit`, `se2recW_eq_msep_unit` | Lean more general in `w` and `α`, narrower in the type of `α` (natural, not real) |
| Mack 1999, weighted factor is conditionally unbiased | `condExp_fhatWrv` | not displayed as a theorem in the source; Lean proves it under (M1) in the `D_k` form |
| Mack 1999, CL2 and `s.e.(f̂_k)² = σ_k² / ∑_j w_jk C_jk^α` | `Mack3W`, `Mack2Factor'`, `condExp_sq_fhatWrv_sub`, `condVar_fhatWrv` | proved from explicit `D_k` assumptions on nonzero weighted volumes; row-to-`D_k` and cross-factor derivations remain open |
| Mack 1999, weighted `σ̂_k²` is unbiased | `condExp_wssWrv`, `condExp_sigma2Wrv` | Lean assumes fixed contributors, nonzero weighted volumes, and the stated conditioned model; zero-weight omission needs a different index set and degrees of freedom |
| Mack 1999, Section 3, tail factor | `tailUltimate`, `tailSe2Step` | convention, no theorem |
| Mack 1993, last-period `σ²` extrapolation | not formalized | convention, no theorem |
| BBMW 2006 / Murphy 1994, conditional-resampling term | `bbmwEstimation`, `mackEstimation_le_bbmwEstimation`, `bbmwEstimation_sub_mackEstimation`, `bbmwEstimation_sub_mackEstimation_le`, `bbmwEstimation_eq_mackEstimation_of_one_factor` | source statement is an estimator; Lean has it as a definition and proves the exact difference against Mack's |
| The two estimators differ strictly | `exists_mackEstimation_lt_bbmwEstimation`, `mackEstimation_lt_bbmwEstimation_Cex` | not in the source; a concrete triangle, every number checked by `norm_num` |
| BBMW 2006, Section 4.3, aggregated over accident years | `bbmwTotalEstimation`, `bbmwTotalEstimation_sub_mackTotalEstimation`, `mackTotalEstimation_le_bbmwTotalEstimation` | definition plus identity; the inequality needs nonnegative ultimates and relative variances |
| Röhr 2016, classical-case display | `rohrMsep`, `rohrMsep_eq_msep`, `rohrProcess_eq_mackProcess`, `rohrParameter_eq_mackEstimation`, `msep_div_ultimate_sq`, `bbmwEstimation_sub_rohrParameter` | formalized from the abstract's display, full text unavailable |
| Röhr 2016, aggregation over accident years | `rohrMsepTotal`, `rohrMsepTotal_eq_msepTotal` | not attributed: the cross terms are Mack's, carried into a definition |
| Merz-Wüthrich 2008, true CDR has conditional mean zero | `RandomTriangle.trueCDR`, `condExp_trueCDR_eq_zero` | identical; Lean's filtration is by development year, the source's by calendar year |
| Merz-Wüthrich 2008, true CDR as a one-step residual | `trueCDR_eq`, `condExp_C_ultimate_of_Mack1`, `condExp_C_of_Mack1_at` | identical under (M1) in the `D_k` form |
| Merz-Wüthrich 2008, observable CDR and its MSEP (Results 3.1-3.3) | `obsCDR`, `RandomTriangle.obsCDRRv`, `obsCDR_eq_reserve_sub` | definition plus one algebraic identity; nothing about its distribution is proved |
| Renshaw-Verrall 1998 / Mack 1991: the marginal sums are score equations | `rowQuasiLogLik`, `colQuasiLogLik`, `hasDerivAt_rowQuasiLogLik`, `hasDerivAt_colQuasiLogLik`, `deriv_rowQuasiLogLik_eq_zero_iff`, `deriv_colQuasiLogLik_eq_zero_iff` | formalized from the marginal-sum system as universally quoted, neither paper available in full text |
| Renshaw-Verrall 1998 / Mack 1991: chain ladder solves the system | `chainLadder_fitted_row_totals`, `chainLadder_fitted_row_totals_eq`, `chainLadder_fitted_column_totals`, `chainLadder_scoreEquations` | identical; the column half needs nonzero development factors |
| Mack 1991, Section 2: uniqueness of the multiplicative fit | `multFit_eq_CLincr`, `mult_cum_eq_CLcum`, `patternCum_mul_fhat` | Lean stronger hypotheses: strict positivity of `a` and `b` and the normalization `∑_{k<n} b_k = 1` |
| Bornhuetter-Ferguson on the chain-ladder pattern | `bfReserve`, `bfUltimate`, `bfReserve_of_ultimate`, `bfUltimate_of_ultimate`, `bfReserve_smul`, `bfReserve_add`, `one_le_cdf`, `bfReserve_nonneg`, `bfReserve_le` | definitions plus deterministic identities; the module names no source display |
| Non-vacuity: degenerate witness | `Witness.X`, `Witness.fhat_unbiased`, `Witness.ultimate_unbiased` | not in any source; certifies the hypotheses are jointly satisfiable |
| Non-vacuity: a nondegenerate Mack model | `NontrivialModel.exists_nontrivial_mack_model`, `NontrivialModel.fhat0_unbiased`, `NontrivialModel.ultimate_unbiased`, `NontrivialModel.var_fhat0`, `NontrivialModel.sigma2_unbiased` | not in any source; `σ_0² = 4 > 0` and the first development step is genuinely random |
| Non-vacuity: independent rows and the row-generated filtration | `IndependenceWitness.exists_independence_witness`, `IndependenceWitness.rowsIndep`, `IndependenceWitness.rowsGenerateD`, `IndependenceWitness.mack1Row`, `IndependenceWitness.mack1_from_rows`, `IndependenceWitness.mack2'_from_rows` | not in any source; realizes Mack 1993 eq. (1)-(2) and the `B_k` filtration on eight outcomes |
| Non-vacuity: the cross-term condition of the total | `NontrivialModel.crossFree_ultimates`, `NontrivialModel.exists_crossFree_nondegenerate` | not in any source; three genuinely random ultimates, conditionally uncorrelated |

Thirty-seven rows.

## The deterministic layer

### Mack 1993, eq. (2): the weighted-average form of the development factor

**Source.** Mack, *Distribution-free calculation of the standard error of chain ladder reserve
estimates*, ASTIN Bulletin 23 (1993) 213-225, eq. (2) as recorded in the module docstring of
`VerifiedReserving/ChainLadder.lean`: the chain-ladder factor is the `C_{i,k}`-weighted average of
the individual development factors `F_{i,k} = C_{i,k+1} / C_{i,k}`.

**Lean.** `fhat_eq_weighted_average (C : ℕ → ℕ → ℝ) (n k : ℕ)`, assuming only that `C i k ≠ 0` for
every `i` in `contributors n k`, gives `fhat C n k = ∑ i ∈ contributors n k, (C i k / S C n k) * F C i k`.
No hypothesis is placed on `S_k`.

**Gap.** Identical. `S_k` may vanish because `x / 0 = 0` makes both sides zero there; only the
individual denominators of `F_{i,k}` need a hypothesis.

### Mack 1993: the degrees of freedom of the variance estimator

**Source.** Mack (1993) divides the weighted sum of squares by `n - k - 2` rather than by the
number `n - k - 1` of contributing accident years, because one degree of freedom is spent
estimating `f̂_k`.

**Lean.** `weighted_sq_dev (C n k f)` proves, for every centre `f` and with every contributing
`C i k` nonzero, that `∑ C_{i,k}(F_{i,k} - f)² = ∑ C_{i,k} F_{i,k}² - 2 f T_k + f² S_k`.
`weighted_sq_dev_at_fhat` adds `S C n k ≠ 0` and gives the collapse at `f = f̂_k`:
`∑ C_{i,k}(F_{i,k} - f̂_k)² = ∑ C_{i,k} F_{i,k}² - S_k f̂_k²`.

**Gap.** Identical. These are the algebraic identities the source uses; the statistical claim they
support is `condExp_sigma2Rv` below.

## Mack's three theorems

### Mack 1993, Theorem 1

**Source.** The chain-ladder ultimate `Ĉ_{i,n-1} = C_{i,d} ∏_{k=d}^{n-2} f̂_k` is an unbiased
estimator of the expected ultimate claims `E[C_{i,n-1}]`, given the data observed so far.

**Lean.** `condExp_ultimate_eq` takes a `RandomTriangle Ω n`, that is random cumulative claims
`C : ℕ → ℕ → Ω → ℝ` together with a filtration `D : ℕ → MeasurableSpace Ω` satisfying `D k ≤` the
ambient σ-algebra, `Monotone D`, and `C i j` strongly `D k`-measurable whenever `j ≤ k`. Its
hypotheses are: `IsFiniteMeasure μ`; `i < n`; `Mack1 X μ f`, that is (M1) in the `D_k`-conditioned
form `μ[C i (k+1) | D k] =ᵐ fun ω => f k * C i k ω` for every `i < n` and every `k`; `hS`, that for
every `k` with `k + 2 ≤ n` the column sum `Srv k` is almost surely nonzero; `hC`, integrability of
every `C j k`; `hf`, integrability of every `fhatRv k`; `hprod`, integrability of every partial
product `ChatRv i m'`. The conclusion is an equality of two conditional expectations,
`μ[ChatRv i i | D (n-1-i)] =ᵐ[μ] μ[C i (n-1) | D (n-1-i)]`. The intermediate
`condExp_ChatRv` gives `μ[ChatRv i m | D (n-1-i)] =ᵐ C_{i,d} ∏_{k ∈ Ico d (d+m)} f k` under the same
hypotheses plus `m ≤ i`, and `condExp_C_of_Mack1` gives the same value for the true claims,
needing only (M1), `i < n` and integrability of the row.

**Gap.** Lean has stronger hypotheses than the source states. Integrability, the finite-measure
instance, and the almost-sure nonvanishing of every column sum along the row are left implicit in
the source. The conclusion is also conditional rather than unconditional: it equates two
conditional expectations given `D_d`, which is the statement actuaries quote, and the
unconditional form follows by integrating only when the measure is a probability measure.

### Mack 1993, Theorem 2

**Source.** The estimators `f̂_0, ..., f̂_{n-2}` are unbiased, `E[f̂_k] = f_k`, and uncorrelated,
`E[f̂_j f̂_k] = f_j f_k` for `j ≠ k`.

**Lean.** Four declarations.
`condExp_fhatRv` assumes `Mack1 X μ f`, that `Srv k ≠ 0` almost surely, integrability of
`C i (k+1)` for every `i` in `contributors n k`, and integrability of `fhatRv k`, and concludes
`μ[fhatRv k | D k] =ᵐ fun _ => f k`. No finiteness of `μ` is needed.
`condExp_fhatRv_mul` assumes `IsFiniteMeasure μ`, `j + 1 ≤ k`, `Mack1`, almost-sure nonvanishing of
`Srv j` and `Srv k`, integrability of both next columns, of `fhatRv j`, of `fhatRv k` and of the
product, and concludes `μ[fhatRv j * fhatRv k | D j] =ᵐ fun _ => f j * f k`.
`integral_fhatRv` and `integral_fhatRv_mul` are the same statements integrated, under
`IsProbabilityMeasure μ`.

**Gap.** Lean has stronger hypotheses: integrability of each variable and of the product, and the
almost-sure nonvanishing of the column sums, none of which the source displays. The
uncorrelatedness is proved for `j < k` only; the Lean statement fixes the order rather than
covering `j ≠ k` symmetrically.

### Mack 1993, proof of Theorem 3: the estimation variance of `f̂_k`

**Source.** Mack (1993), proof of Theorem 3, and Mack (1999) in the form
`s.e.(f̂_k)² = σ̂_k² / S_k`: the estimation variance of the development factor is `σ_k² / S_k`.

**Lean.** `condExp_sq_fhatRv_sub` assumes `IsFiniteMeasure μ`; `Mack3 X μ f σ2`, that is (M3) in the
`D_k`-conditioned form `μ[fun ω => (eps f i k ω)² | D k] =ᵐ fun ω => σ2 k * C i k ω` for `i < n` and
every `k`, with `eps f i k = C i (k+1) - f k * C i k`; `Mack2' X μ f`, that is
`μ[fun ω => eps f i k ω * eps f j k ω | D k] =ᵐ 0` for distinct `i, j` in `contributors n k`;
`Srv k ≠ 0` almost surely; integrability of every product `eps i k * eps j k`; and integrability of
`(fhatRv k - f k)²`. The conclusion is `μ[fun ω => (fhatRv k ω - f k)² | D k] =ᵐ fun ω => σ2 k / Srv k ω`,
a pointwise quotient, not a constant.

**Gap.** Identical to the source's step, with integrability and almost-sure nonvanishing of `S_k`
added. (M1) is not used. The conclusion carries `S_k(ω)` in the denominator because `S_k` is a
random variable that happens to be `D_k`-measurable.

### Mack 1993, proof of Theorem 3: `σ̂²_k` is unbiased

**Source.** `σ̂_k² = (n-k-2)^{-1} ∑_i C_{i,k}(F_{i,k} - f̂_k)²` is unbiased for `σ_k²`, which is why
the divisor is `n - k - 2`.

**Lean.** `weighted_sq_dev_eps` is the deterministic step: with every contributing `C i k` nonzero
and `S_k ≠ 0`, for any real `f`,
`∑ C_{i,k}(F_{i,k} - f̂_k)² = ∑ (C_{i,k+1} - f C_{i,k})² / C_{i,k} - S_k (f̂_k - f)²`.
`condExp_wssRv` assumes `IsFiniteMeasure μ`, `k + 2 ≤ n`, `Mack3`, `Mack2'`, that each contributing
`C i k` is almost surely nonzero, that `Srv k` is almost surely nonzero, and four integrability
hypotheses (the residual products, `eps² / C i k`, `(fhatRv k - f k)²`, and
`Srv k * (fhatRv k - f k)²`), and concludes `μ[wssRv k | D k] =ᵐ fun _ => ((n : ℝ) - k - 2) * σ2 k`.
`condExp_sigma2Rv` is the same with `k + 3 ≤ n` and concludes `μ[sigma2Rv k | D k] =ᵐ fun _ => σ2 k`.

**Gap.** Lean has stronger hypotheses. It needs `k + 3 ≤ n`, so that at least two accident years
contribute and the divisor `n - k - 2` is positive, and it needs every contributing `C_{i,k}` to be
almost surely nonzero because the identity divides by it. The source states neither. (M1) is not
used; only (M3) and (M2') are.

### Process variance along a row

**Source.** Mack (1993) computes the process-variance part of the prediction error by iterating
the conditional variance along the row.

**Lean.** `procVar c f σ2 d` is a definition by recursion: `procVar ... 0 = 0` and
`procVar ... (m+1) = (f (d+m))² * procVar ... m + σ2 (d+m) * (c * ∏ l ∈ Ico d (d+m), f l)`, with
closed form `procVar_eq_sum`. `condVar_C_eq_procVar` assumes `IsFiniteMeasure μ`, `i < n`, `Mack1`,
`Mack3`, and integrability of every `C i k`, of every `(C i k)²`, of every `(eps f i k)²` and of
every `C i k * eps f i k`, and concludes that the conditional variance
`μ[C_{i,d+m}² | D_d] - (μ[C_{i,d+m} | D_d])²` equals `procVar (C i d ω) f σ2 d m` almost everywhere.

**Gap.** Identical, with integrability added. The process variance is a definition and the theorem
identifies it with the conditional variance, so the recursion is not assumed.

### Mack 1993, Theorem 3, exact conditional form

**Source.** Mack (1993), Theorem 3: an estimator of the mean squared error of prediction of the
reserve `R̂_i`, split into a process part and an estimation part.

**Lean.** `condExp_sq_sub_of_stronglyMeasurable` is the general decomposition: for a
`D`-measurable predictor `P` of an integrable `Y`, with `Y²`, `P²` and `P * Y` integrable and
`D ≤` the ambient σ-algebra on a finite measure,
`μ[(P - Y)² | D] =ᵐ (μ[Y² | D] - (μ[Y | D])²) + (P - μ[Y | D])²`.
`condMsep_eq` instantiates it. Its hypotheses are: `IsFiniteMeasure μ`; a sub-σ-algebra `D` of the
observed data with `D ≤` the ambient one; `hPmeas`, that `ChatRv i m` is strongly `D`-measurable;
`hfut1` and `hfut2`, that the conditional mean and the conditional second moment of
`C_{i,d+m}` given `D` agree almost everywhere with those given `D_d`; `i < n`; `Mack1`; `Mack3`;
integrability of every `C i k`, `(C i k)²`, `(eps f i k)²` and `C i k * eps f i k`; and
integrability of `(ChatRv i m)²` and of `ChatRv i m * C_{i,d+m}`. The conclusion is
`μ[(ChatRv i m - C_{i,d+m})² | D] =ᵐ procVar (C i d ω) f σ2 d m + (ChatRv i m ω - C i d ω * ∏ l ∈ Ico d (d+m), f l)²`.

**Closure.** The base theorem `condMsep_eq` exposes "the observed data tells you nothing more about
row `i`'s future than row `i`'s own history does" as `hfut1` and `hfut2`.
`condExp_C_obsSigma_eq_D` and `condExp_sq_C_obsSigma_eq_D` derive both on `obsSigma` from
`RowsGenerateD`, `RowsIndep` and the corresponding integrability hypotheses.
`condMsep_eq_of_rows` packages the exact result from `Mack1Row`, `Mack3Row`, `RowsIndep`,
`RowsGenerateD` and square integrability. The conclusion is an exact identity about the true
conditional MSEP, not the plug-in formula of the source's display.

### Mack 1993, Theorem 3, plug-in estimator

**Source.** Mack (1993), Theorem 3, displayed estimator:
`msep(R̂_i) = Ĉ_{i,n-1}² ∑_{k=d}^{n-2} (σ̂_k²/f̂_k²)(1/Ĉ_{i,k} + 1/S_k)`.

**Lean.** `msep C n i` is exactly that expression as a definition on a deterministic triangle.
`mackProcess C n i m` is `procVar` with `f̂` and `σ̂²` substituted. `mackEstimation C n i` is
`Ĉ_{i,n-1}² ∑_k σ̂_k²/f̂_k²/S_k`, and its docstring records how it arises: replace `(f̂_k - f_k)²`
by its conditional expectation `σ_k²/S_k`, drop the cross terms, and plug in the estimators.

**Gap.** The source statement is an estimator; Lean has it as a definition and proves algebraic
identities about it. No theorem in the library says `msep` is unbiased for, or consistent for, the
conditional MSEP of `condMsep_eq`. The conditional-resampling step that produces `mackEstimation`
is recorded in a docstring, not proved.

### Mack's closed form is process variance plus estimation error

**Source.** Not displayed as such in Mack (1993); it is what reading the closed form through
Röhr's split gives.

**Lean.** `msep_eq_mackProcess_add_mackEstimation (C n i)` assumes `i ≤ n - 1`, that
`fhat C n k ≠ 0` for every `k` in `Ico (n-1-i) (n-1)`, and that `Chat C n i k ≠ 0` on the same
range, and concludes `msep C n i = mackProcess C n i i + mackEstimation C n i`.
`msep_eq_mackProcess_add_mackEstimation_of_lt` is the same with `i < n` and a self-contained proof.

**Gap.** Identical to the informal statement, with the two nonvanishing hypotheses the algebra
needs. Both hold on any real triangle with positive entries.

### Mack 1993, Corollary (total reserve), plug-in

**Source.** Mack (1993), Corollary to Theorem 3: the MSEP of the total reserve `R̂ = ∑_i R̂_i` is
estimated by `∑_i msep_i + ∑_i Ĉ_{i,n-1} (∑_{j>i} Ĉ_{j,n-1}) ∑_{k=d_i}^{n-2} 2 σ̂_k²/(f̂_k² S_k)`,
the cross terms running over the older year's remaining development factors.

**Lean.** `msepTotal C n = ∑ i ∈ range n, msep C n i + ∑ i ∈ range n, mackCross C n i`, with
`mackCross C n i = ultimate C n i * laterUltimates C n i * (2 * rowSum C n i)` and
`rowSum C n i = ∑ k ∈ Ico (n-1-i) (n-1), relVar C n k`. `mackTotalEstimation` is the same sum with
`msep` replaced by `mackEstimation`. All are definitions.

**Gap.** The source statement is an estimator; Lean has it as a definition. Nothing is proved
about its relation to the true total MSEP.

### Mack 1993, Corollary, exact form

**Source.** The object the Corollary approximates: the conditional MSEP of the summed ultimates.

**Lean.** `CondCrossFree μ D s Y` is the hypothesis that for distinct `i, j` in the finite set `s`
the centred targets are conditionally uncorrelated, `μ[(Y i - μ[Y i | D])(Y j - μ[Y j | D]) | D] =ᵐ 0`.
`condMsepTotal_eq` assumes `IsFiniteMeasure μ`; `D ≤` the ambient σ-algebra; `i < n` for every `i`
in `s`; strong `D`-measurability of each `ChatRv i i`; `MemLp _ 2 μ` for each prediction and for
every `C i k` with `i` in `s`; `CondCrossFree μ D s (fun i => C i (n-1))`; the two "no further
information" hypotheses `hfut1` and `hfut2` for each `i` in `s`; `Mack1`; and `Mack3`. It concludes
`μ[(∑_i Ĉ_i - ∑_i C_i)² | D] =ᵐ (∑_i procVar (C i d_i ω) f σ2 d_i i) + (∑_i (Ĉ_i - C_{i,d_i} ∏ f))²`.
`sum_procVar_le_condMsepTotal` is the corollary that the left side dominates `∑_i procVar_i`.

**Closure.** The base theorem `condMsepTotal_eq` exposes `CondCrossFree` and the per-row `hfut`
conditions. `condCrossFree_of_rows` derives the former from `RowsIndep` and square integrability,
while `condExp_obsSigma_eq_D` supplies the latter from `RowsGenerateD`, `RowsIndep` and
integrability. `condMsepTotal_eq_of_rows` packages the exact total result from the row-conditioned
assumptions, `RowsGenerateD`, independence and square integrability. The eight-outcome
independent-row witness checks both derived conditions, but does not yet instantiate this packaged
theorem because it does not supply `Mack3Row`. Square integrability is carried as `MemLp _ 2 μ` so
that Hölder supplies the product integrability, which is a convenience, not a weakening.

### Mack 1993, Corollary: the plug-in has the exact shape

**Lean.** `msepTotal_eq_sum_mackProcess_add_mackTotalEstimation (C n)` assumes that for every `i`
in `range n` the development factors and the projections along that row are nonzero, and concludes
`msepTotal C n = ∑ i ∈ range n, mackProcess C n i i + mackTotalEstimation C n`.

**Gap.** Identical to the informal claim that the plug-in mirrors the exact decomposition. It is
an identity of the deterministic layer, not a statement about estimation.

## The assumptions and where they come from

### Mack 1993, eq. (1) and (2), pp. 214-215: (M1) and (M3), row form and `D_k` form

**Source.** Mack states his assumptions on one accident year at a time. Eq. (1), p. 214:
`E[C_{i,k+1} | C_{i,0}, ..., C_{i,k}] = f_k C_{i,k}`. The variance assumption is the same
conditioning with `Var(C_{i,k+1} | C_{i,0}, ..., C_{i,k}) = σ_k² C_{i,k}`. Eq. (2), p. 215, is the
separate assumption that the accident years are independent. The proof of Theorem 2, pp. 215-216,
works with the filtration `B_k` of everything observed up to development year `k` and passes from
the row-conditioned form to the `B_k`-conditioned form in one sentence.

**Lean.** Both forms are definitions.
`Mack1Row X μ f` is `μ[C i (k+1) | rowSigma i k] =ᵐ fun ω => f k * C i k ω` for `i < n` and every
`k`, where `rowSigma i k = ⨆ j, ⨆ _ : j ≤ k, comap (C i j)`.
`Mack3Row X μ f σ2` is the same conditioning applied to `(eps f i k)²`.
`Mack1` and `Mack3` are the `D_k`-conditioned forms, with `D k` the filtration carried by the
`RandomTriangle` structure.
`RowsIndep X μ` is `iIndep (fun i => rowSigmaAll i) μ`, Mack's (M2).
`RowsGenerateD X` is `∀ k, D k = ⨆ i, rowSigma i k`.
`mack1_of_mack1Row` assumes `IsFiniteMeasure μ`, `RowsGenerateD`, `RowsIndep`, `Mack1Row` and
integrability of every `C i k`, and concludes `Mack1`. `mack3_of_mack3Row` assumes the same with
`Mack3Row` and integrability of every `(eps f i k)²`, and concludes `Mack3`.

**Gap.** Lean proves the passage the source takes in one sentence, and adds two hypotheses the
source leaves as a reading of notation: `RowsGenerateD`, that the filtration really is the join of
the rows' histories, and integrability. The `RandomTriangle` structure does not force
`RowsGenerateD`, so it must be supplied; `IndependenceWitness.rowsGenerateD` supplies it on the
finite witness by construction.

### The general fact behind the passage

**Source.** Not in Mack. Mathlib has the case `m₁ = ⊥` as `condExp_indep_eq`.

**Lean.** `condExp_sup_of_indep` assumes `IsFiniteMeasure μ`, `m₁ ≤ m₁'`, `m₁' ≤ m0`, `m₂ ≤ m0`,
`Indep m₁' m₂ μ`, `f` strongly `m₁'`-measurable and integrable, and concludes
`μ[f | m₁ ⊔ m₂] =ᵐ μ[f | m₁]`. It is proved from the characterisation of conditional expectation on
the π-system of rectangles `a ∩ b`, using `setIntegral_inter_of_indep`.

**Gap.** New relative to the source and to mathlib. The join version is what the row-to-`D_k`
passage needs.

### (M2'), the cross-term condition

**Source.** Mack does not display (M2') as an assumption; it is a step inside the variance
calculation, supplied by independence across accident years.

**Lean.** `Mack2' X μ f` is a definition and is a hypothesis of `condExp_sq_fhatRv_sub`,
`condExp_wssRv` and `condExp_sigma2Rv`. `mack2'_of_rows` assumes `IsFiniteMeasure μ`,
`RowsGenerateD`, `RowsIndep`, `Mack1Row`, integrability of every `C i j` and of every product
`eps f i k * eps f j k`, and concludes `Mack2' X μ f`.

**Gap.** Lean derives what the source leaves implicit. Note the direction of the dependency: the
derivation uses the row-conditioned (M1row), not the `D_k`-conditioned (M1), so the two forms of
the first assumption are both in play. The variance theorems still take `Mack2'` as a hypothesis
rather than requiring `RowsIndep`, so a caller who wants the derived version must apply
`mack2'_of_rows` explicitly.

## Mack 1999

### The recursion equals the 1993 closed form, `α = 1` with unit weights

**Source.** Mack, *The standard error of chain ladder reserve estimates: recursive calculation and
inclusion of a tail factor*, ASTIN Bulletin 29 (1999) 361-366. The recursion displayed below
eq. (*) is
`s.e.(Ĉ_{i,k+1})² = Ĉ_{i,k}²(s.e.(F_{i,k})² + s.e.(f̂_k)²) + s.e.(Ĉ_{i,k})² f̂_k²`, with
`s.e.(F_{i,k})² = σ̂_k²/Ĉ_{i,k}` and `s.e.(f̂_k)² = σ̂_k²/S_k`. The paper says the recursion leads to
the 1993 closed form.

**Lean.** `se2rec C n i` is that recursion started at `0` on the latest diagonal.
`se2rec_eq_closed (C n i m)` assumes `fhat C n k ≠ 0` for every `k` in `Ico (n-1-i) (n-1-i+m)` and
gives the truncated closed form. `se2rec_eq_msep (C n i)` assumes `i ≤ n - 1` and
`fhat C n k ≠ 0` for every `k` in `Ico (n-1-i) (n-1)`, and concludes `se2rec C n i i = msep C n i`.

**Gap.** Lean has a stronger hypothesis: nonzero development factors along the row. The paper
states the identity without a side condition. The hypothesis is real, not an artefact: the step
divides by `f̂_k²`.

### Equation (*) and the recursion for general weights and exponent

**Source.** Mack (1999) widens the factor estimator to
`f̂_k = (∑_i w_{ik} C_{ik}^α F_{ik})/(∑_i w_{ik} C_{ik}^α)` with `w_{ik} ∈ [0,1]` and `α ∈ {0,1,2}`,
and displays eq. (*),
`s.e.(Ĉ_{in})² = Ĉ_{in}² ∑_k (σ̂_k²/f̂_k²)(1/(w_{ik} Ĉ_{ik}^α) + 1/∑_j w_{jk} C_{jk}^α)`,
with the matching recursion below it.

**Lean.** `SW`, `TW`, `fhatW`, `sigma2W`, `ChatW`, `ultimateW`, `mackTermW`, `msepW` and `se2recW`
are definitions for an arbitrary weight function `w : ℕ → ℕ → ℝ` and an arbitrary exponent
`α : ℕ`. `se2recW_eq_msepW (C n w α i)` assumes `i ≤ n - 1` and `fhatW C n w α k ≠ 0` for every `k`
in `Ico (n-1-i) (n-1)`, and concludes `se2recW C n w α i i = msepW C n w α i`.
`fhatW_eq_weighted_average` needs no hypothesis at all; `weighted_sq_devW_at_fhatW` needs
`SW C n w α k ≠ 0`. `msepW_unit`, `se2recW_unit` and `se2recW_eq_msep_unit` collapse to the 1993
objects, each assuming that every contributing `C l j` is nonzero.

**Gap.** Lean is more general in one direction and narrower in another. Mack's restrictions
`w_{ik} ∈ [0,1]` and `α ∈ {0,1,2}` are not imposed, because no identity uses them. Against that,
`α` has type `ℕ`, so a non-integer exponent cannot be expressed. The nonvanishing hypothesis on
the weighted development factors is the same addition as in the unit-weight case.

### The weighted estimator is conditionally unbiased

**Source.** Mack (1999) does not display this as a theorem; it is the property the weighted family
is chosen for.

**Lean.** `condExp_fhatWrv (X w α f k)` assumes each weight `w i k` is strongly `D k`-measurable,
`Mack1 X μ f`, that almost surely every contributing `C i k` is nonzero, that the weighted column
sum `SWrv w α k` is almost surely nonzero, integrability of each `C i (k+1)`, of each
`gW w α i k * C i (k+1)` and of `fhatWrv w α k`, and concludes
`μ[fhatWrv w α k | D k] =ᵐ fun _ => f k`. Here `gW w α i k = w i k * (C i k)^α / C i k` is the
`D_k`-measurable multiplier, and no finiteness of `μ` is needed.

**Gap.** Not in the source as a display, so there is no statement to compare against; the Lean
statement is the natural generalization of `condExp_fhatRv`, with the extra hypothesis that the
contributing entries are almost surely nonzero, which `α = 0` cannot do without.

### Weighted estimation variance and unbiasedness of `sigma2W`

**Source.** Mack (1999), pp. 362-363, gives CL2 as
`Var(F_{ik} | observed history) = σ_k²/(w_{ik} C_{ik}^α)`, displays
`s.e.(f̂_k)² = σ̂_k²/∑_j w_{jk} C_{jk}^α`, and defines
`σ̂_k² = (n-k-2)⁻¹ ∑_i w_{ik} C_{ik}^α(F_{ik}-f̂_k)²`.

**Lean.** `Mack3W X μ w α f σ2` is CL2 in conditional second-moment form around `f k`, and
`Mack2Factor' X μ f` states conditional uncorrelatedness of different accident years' factor
residuals. `condExp_sq_fhatWrv_sub` assumes both, predictable weights, almost-surely nonzero
claims, weighted volumes and weighted column sum, plus the listed integrability conditions, and
concludes
`μ[(fhatWrv w α k - f k)² | D k] =ᵐ fun ω => σ2 k / SWrv w α k ω`.
Given the conditional-mean equality proved separately by `condExp_fhatWrv`, `condVar_fhatWrv`
identifies the same expression with mathlib's conditional variance.
`condExp_wssWrv` proves that the weighted residual sum of squares has conditional expectation
`(n-k-2)σ2 k`; for `k+3≤n`, `condExp_sigma2Wrv` divides by the nonzero degrees of freedom and
concludes `μ[sigma2Wrv w α k | D k] =ᵐ fun _ => σ2 k`.

**Gap.** Mack permits weights in `[0,1]`, but CL2 divides by `w_{ik}C_{ik}^α`. A zero-weight cell
is naturally omitted from the sample. The current Lean estimator keeps the fixed
`contributors n k` set and denominator `n-k-2`, so the theorem requires every contributing
weighted volume to be nonzero. A theorem allowing zero weights needs an active-contributor set
and denominator `active.card-1`. `Mack3W` is conditioned on the full `D_k`; deriving it from the
paper's row-conditioned CL2 and independence is not included. Lean also permits predictable
random weights; deterministic weights are a special case, while weights chosen after observing
`F_{ik}` are not covered.

### Section 3: the tail factor

**Source.** Mack (1999), Section 3, attaches a tail factor to the ultimate and carries variance
parameters for it through the recursion. The paper gives no estimator for the tail factor or for
its variance parameters; the actuary supplies them.

**Lean.** `tailUltimate C n w α i ftail` and `tailSe2Step C n w α i ftail sigma2tail Stail` are
definitions. No theorem in the development mentions either.

**Gap.** Convention, no theorem.

### The last-period variance extrapolation

**Source.** Mack (1993) cannot estimate `σ_{n-2}²` because only one accident year contributes, and
proposes an extrapolation rule.

**Lean.** Not formalized. `sigma2 C n (n-2)` returns `0` because its divisor `n - k - 2` is zero
and `1 / 0 = 0`; `Cex_sigma2_2` records this on the counterexample triangle. No theorem uses the
value.

**Gap.** Convention, no theorem. The library keeps it outside the theorems on purpose, and the
Lean definition's value at that index is an artefact of the division convention rather than an
implementation of Mack's rule.

## The variant catalogue

### BBMW 2006 and Murphy 1994: the conditional-resampling term

**Source.** Buchwalder, Bühlmann, Merz and Wüthrich (2006), the conditional-resampling estimator of
the estimation error, which Murphy (1994) also reaches:
`Ĉ_{i,n-1}² (∏_k (1 + a_k) - 1)` with `a_k = σ̂_k²/(f̂_k² S_k)`. Buchwalder et al. and Wüthrich and
Merz (2008, Remark 3.13) describe Mack's `Ĉ² ∑_k a_k` as the linear approximation from below of
theirs; the two-factor remainder `a_1 a_2` appears in Mack, Quarg and Braun (2006, p. 552);
Buchwalder et al., Table 5, reports the two as numerically close.

**Lean.** `relVar C n k` is `a_k` and `bbmwEstimation C n i` is the product form, both definitions.
`mackEstimation_le_bbmwEstimation` assumes `0 ≤ relVar C n k` for every `k` in `Ico (n-1-i) (n-1)`
and concludes `mackEstimation C n i ≤ bbmwEstimation C n i`.
`bbmwEstimation_sub_mackEstimation` needs no hypothesis and gives the exact difference
`Ĉ² (∏_k (1 + a_k) - 1 - ∑_k a_k)`.
`bbmwEstimation_eq_mackEstimation_of_one_factor` assumes `2 ≤ n` and gives equality for the
accident year `i = 1`, which has a single development factor.
`bbmwEstimation_sub_mackEstimation_le` assumes the same nonnegativity and bounds the difference by
`Ĉ² (exp(∑_k a_k) - 1 - ∑_k a_k)`.
`remainder_eq_zero_of_subsingleton_support` gives equality whenever at most one `a_k` is nonzero.

**Gap.** Both source statements are estimators; Lean has them as definitions and proves the exact
algebraic relation between them. The nonnegativity of `a_k` is a hypothesis rather than a
consequence: the library does not assume the triangle entries are nonnegative, so it does not
derive `0 ≤ relVar C n k` from anything. Which estimator has better statistical properties is
outside the library, and the docstring says so.

### The two estimators differ strictly

**Source.** Not in any source as a proof; the disagreement is discussed but not settled by a
worked counterexample.

**Lean.** `Cex` is a four-by-four triangle. `Cex_S0`, `Cex_T0`, `Cex_fhat0`, `Cex_sigma2_0`,
`Cex_relVar0` and their siblings evaluate every quantity by `norm_num`.
`mackEstimation_lt_bbmwEstimation_Cex` concludes `mackEstimation Cex 4 3 < bbmwEstimation Cex 4 3`,
and `exists_mackEstimation_lt_bbmwEstimation` is the existential form. On that triangle
`a_0 = 1/297`, `a_1 = 1/2809`, `a_2 = 0`.

**Gap.** New relative to the sources. It settles that the two are different estimators rather than
two presentations of one.

### Aggregated over accident years

**Source.** Buchwalder, Bühlmann, Merz and Wüthrich (2006), Section 4.3, aggregate the
conditional-resampling estimator with the cross term `2 Ĉ_i Ĉ_j (∏_{k ∈ row i}(1 + a_k) - 1)`.

**Lean.** `bbmwCross` and `bbmwTotalEstimation` are definitions.
`bbmwTotalEstimation_sub_mackTotalEstimation` needs no hypothesis and gives the difference as
`∑_i (Ĉ_i² + 2 Ĉ_i ∑_{j>i} Ĉ_j)(rowProd_i - rowSum_i)`.
`mackTotalEstimation_le_bbmwTotalEstimation` assumes `0 ≤ ultimate C n i` for every `i` in
`range n` and `0 ≤ relVar C n k` for every `k`, and concludes the inequality.

**Gap.** Definitions plus an identity, as in the single-year row. The inequality's nonnegativity
hypotheses are stronger than they need to be in one place: `ha` quantifies over all `k`, not only
over the rows in play.

### Röhr 2016

**Source.** Röhr, *Chain ladder and error propagation*, ASTIN Bulletin 46 (2016) 293-330. The full
text was not available; the module docstring records that what is formalized is the abstract's
statement that in the classical case treated by Mack (1993) the mean squared prediction error
divided by the squared estimated ultimate loss can be written as `∑_j û_j²`, where `û_j` measures
the relative uncertainty around the `j`-th development factor and the proportion of the estimated
ultimate loss that it affects, together with the abstract's split into process error and parameter
error, taken in the form `û_k² = σ̂_k²/(f̂_k² Ĉ_{i,k}) + σ̂_k²/(f̂_k² S_k)`.

**Lean.** `rohrRelProcess`, `rohrRelParam`, `rohrRelVar`, `rohrProcess`, `rohrParameter` and
`rohrMsep` are definitions.
`rohrMsep_eq_rohrProcess_add_rohrParameter` is the split, by construction.
`rohrParameter_eq_mackEstimation` and `rohrRelParam_eq_relVar` need no hypothesis.
`rohrProcess_eq_mackProcess (C n i)` assumes `i ≤ n - 1`, `fhat C n k ≠ 0` and `Chat C n i k ≠ 0`
for every `k` in `Ico (n-1-i) (n-1)`, and concludes `rohrProcess C n i = mackProcess C n i i`.
`rohrMsep_eq_msep` needs no hypothesis at all and concludes `rohrMsep C n i = msep C n i`.
`msep_div_ultimate_sq` assumes `ultimate C n i ≠ 0` and gives the abstract's relative display.
`bbmwEstimation_sub_rohrParameter` needs no hypothesis and exhibits the parameter term as the
first-order part of the conditional-resampling term.

**Gap.** Formalized from the abstract's display, full text unavailable. The paper's general
claims-development-result formulas between two arbitrary future horizons are not formalized. That
`rohrMsep_eq_msep` needs no side condition is a consequence of Lean's division convention:
`σ̂_k²/(f̂_k² Ĉ_{i,k})` and `(σ̂_k²/f̂_k²)(1/Ĉ_{i,k})` are the same term of the language.

### Röhr's aggregation over accident years

**Source.** Röhr's own aggregation could not be checked against the source.

**Lean.** `rohrMsepTotal C n = ∑ i ∈ range n, rohrMsep C n i + ∑ i ∈ range n, mackCross C n i` is a
definition whose cross terms are Mack's, and `rohrMsepTotal_eq_msepTotal` proves it equals
`msepTotal C n` with no hypothesis.

**Gap.** Not attributed. The definition is labelled as carrying Mack's cross terms rather than
Röhr's, and the docstring says so.

## The one-year claims development result

### Merz-Wüthrich 2008: the true CDR has conditional mean zero

**Source.** Merz and Wüthrich, *Modelling the claims development result for solvency purposes*,
CAS E-Forum (2008). The true claims development result is
`CDR_i(k) = E[C_{i,n-1} | D_k] - E[C_{i,n-1} | D_{k+1}]` and has conditional mean zero.

**Lean.** `RandomTriangle.trueCDR X μ i k` is that difference, a definition.
`condExp_trueCDR_eq_zero` assumes only `IsFiniteMeasure μ` and concludes
`μ[trueCDR μ i k | D k] =ᵐ 0`, for every accident year and every step. It uses only that `D` is a
filtration inside the ambient σ-algebra. No integrability of `C_{i,n-1}` is needed for the identity
as stated, since mathlib's conditional expectation is `0` off the integrable case; the statement
carries its intended meaning exactly when `C_{i,n-1}` is integrable.

**Gap.** Identical, and Lean's hypotheses are weaker than the source's, which assumes a model.
The filtration differs in indexing: Lean's `D_k` is by development year, the source indexes
information by calendar year, `D_I = {C_{i,j} : i + j ≤ I}`. The martingale statement is the same
tower property in either filtration, and the docstring records the difference.

### Merz-Wüthrich 2008: the true CDR as a one-step residual

**Lean.** `trueCDR_eq` assumes `IsFiniteMeasure μ`, `i < n`, `k < n - 1`, `Mack1 X μ f` and
integrability of every `C i j`, and concludes
`trueCDR μ i k =ᵐ fun ω => (∏ j ∈ Ico (k+1) (n-1), f j) * (f k * C i k ω - C i (k+1) ω)`.
`condExp_C_of_Mack1_at` and `condExp_C_ultimate_of_Mack1` are the supporting iterations of (M1)
from an arbitrary starting development year.

**Gap.** Identical under (M1) in the `D_k` form, with integrability added. Stated in the
development-year filtration, as above.

### Merz-Wüthrich 2008: the observable CDR

**Source.** The observable CDR is the difference of the chain-ladder ultimates computed from the
triangle with `n` diagonals and from the triangle a year later with every development factor
re-estimated. The paper's Results 3.1 to 3.3 give its conditional mean squared error of prediction,
which is what a Solvency II one-year reserve risk figure reports.

**Lean.** `obsCDR C n i = ultimate C n i - ultimate C (n+1) i` and
`RandomTriangle.obsCDRRv` are definitions. `obsCDR_eq_reserve_sub` needs no hypothesis and gives
the form the source displays: opening reserve minus the payments of the year and the closing
reserve. Nothing else is proved.

**Gap.** Differently scoped, deliberately. Results 3.1 to 3.3 rest on an approximation step of the
same kind as Mack's, treating estimated factors as resampled and dropping second-order residual
terms. That step is not formalized, so no expectation, variance or MSEP statement about `obsCDR`
appears.

## Chain ladder as a generalized linear model

### The marginal sums are score equations

**Source.** Renshaw and Verrall, *A stochastic model underlying the chain-ladder technique*,
British Actuarial Journal 4 (1998) 903-923, Section 3, and Mack, *A simple parametric model for
rating automobile insurance or estimating IBNR claims reserves*, ASTIN Bulletin 21 (1991) 93-109,
Section 2. Neither paper was available in full text; the module docstring records that what is
formalized is the marginal-sum system as it is universally quoted, citing also England and Verrall,
British Actuarial Journal 8 (2002) 443-518, Section 2.3, and Wüthrich and Merz (2008), Section 2.3.
The displayed equations are therefore named by section, not by number.

**Lean.** `rowQuasiLogLik` and `colQuasiLogLik` are the quasi-Poisson log-likelihoods of one row
and one column as functions of a single parameter, with the dispersion set to `1`.
`hasDerivAt_rowQuasiLogLik (C n i b t)` assumes `t ≠ 0` and `b k ≠ 0` for every `k` in `obsRow n i`,
and gives the derivative as the row marginal residual divided by `t`; the column counterpart is
symmetric. `deriv_rowQuasiLogLik_eq_zero_iff` assumes `a i ≠ 0` and the same nonvanishing of `b`,
and states the equivalence between the vanishing of the derivative at `a i` and the row
marginal-sum equation `∑_k multFit a b i k = ∑_k incr C i k`; `deriv_colQuasiLogLik_eq_zero_iff`
is the column form.

**Gap.** Formalized from the marginal-sum system, not from a numbered display, because neither
paper was available in full text. The dispersion `φ` is set to `1` rather than carried and
cancelled; the docstring explains that it cancels, which is why the ODP fit is the Poisson fit.

### Chain ladder solves the marginal-sum system

**Lean.** `chainLadder_fitted_row_totals (C n i)` assumes only `i < n` and gives
`∑ k ∈ obsRow n i, CLincr C n i k = C i (n-1-i)`; `chainLadder_fitted_row_totals_eq` restates it as
the row marginal-sum equation. `chainLadder_fitted_column_totals (C n k)` assumes `k < n` and
`fhat C n j ≠ 0` for every `j < n - 1`, and gives the column equation.
`chainLadder_scoreEquations` packages both as `ScoreEquations (CLincr C n) C n` under the same
nonvanishing hypothesis.

**Gap.** Identical. The row half needs no hypothesis because the fitted values telescope; the
column half is a downward induction whose step is the definition of `f̂_k` as the ratio of the two
column sums, and it needs the development factors used to be nonzero, which also gives the nonzero
column sums.

### Mack 1991, Section 2: uniqueness of the multiplicative fit

**Source.** Mack (1991), Section 2: a multiplicative fit satisfying the marginal-sum equations is
the chain-ladder fit.

**Lean.** `multFit a b i k = a i * b k`, `PatternNormalized b n` is `∑ k ∈ range n, b k = 1`, and
`patternCum b k = ∑ j ∈ range (k+1), b j`. `multFit_eq_CLincr (C n i k a b)` assumes
`0 < a j` for every `j < n`, `0 < b j` for every `j < n`, `PatternNormalized b n`,
`ScoreEquations (multFit a b) C n`, `i < n` and `i + k ≤ n - 1`, and concludes
`multFit a b i k = CLincr C n i k`. `mult_cum_eq_CLcum` is the cumulative form and
`patternCum_mul_fhat` is the step identifying `B_{k+1}/B_k` with `f̂_k`.

**Gap.** Lean has stronger hypotheses: strict positivity of both parameter vectors on the observed
range, and the identifiability constraint `∑_{k<n} b_k = 1`. The source's statement carries the
normalization; the strict positivity is what the Lean proof needs to divide, and whether the source
assumes it or derives it could not be checked, the paper not being available in full text. The
conclusion is cell by cell on observed cells, not a statement about the parameters themselves,
which are identified only up to the normalization.

## Bornhuetter-Ferguson

**Source.** The Bornhuetter-Ferguson method applies the chain-ladder development pattern to an a
priori ultimate `U`: `R^BF_i = U (1 - 1/∏_{k=d}^{n-2} f̂_k)`. The module docstring names no
published display.

**Lean.** `cdf C n i = ∏ k ∈ Ico (n-1-i) (n-1), fhat C n k`, `bfReserve C n i U = U * (1 - 1/cdf C n i)`
and `bfUltimate C n i U = C i (n-1-i) + bfReserve C n i U` are definitions.
`bfReserve_smul` and `bfReserve_add` need no hypothesis and give linearity in `U`.
`bfUltimate_of_ultimate` and `bfReserve_of_ultimate` assume `cdf C n i ≠ 0` and conclude that BF
with the chain-ladder ultimate as prior returns the chain-ladder ultimate and reserve exactly.
`one_le_cdf` assumes `1 ≤ fhat C n k` for every `k` in `Ico (n-1-i) (n-1)` and concludes
`1 ≤ cdf C n i`; `bfReserve_nonneg` and `bfReserve_le` add `0 ≤ U` and bound the reserve in
`[0, U]`.

**Gap.** Definitions plus deterministic identities. The module names no source display, so there
is no numbered statement to compare against; nothing stochastic is claimed about the method.

## Non-vacuity

### The degenerate witness

**Lean.** `Witness.X n` is the triangle `C_{i,k} = 100 · 2^k` on the one-point probability space
with the trivial filtration `D k = ⊤`, satisfying `Mack1` with `f_k = 2`, `Mack3` and `Mack2'` with
`σ_k² = 0`, and with every column sum nonzero for `k + 2 ≤ n`. `Witness.fhat_unbiased` and
`Witness.ultimate_unbiased` instantiate Theorems 2 and 1 on it. CI runs the file.

**Gap.** Not in any source. It certifies that the hypothesis set is not contradictory. It has no
randomness, so on its own it does not certify that the theorems say anything.

### The nondegenerate model

**Lean.** `NontrivialModel.X` is a `RandomTriangle Ω 3` on eight equally likely outcomes with an
independent `±1` shock per accident year, `C_{i,0} = 100` and `C_{i,k} = 100 · 2^k (1 + ξ_i/10)`
for `k ≥ 1`, with `D_0 = ⊥` and `D_k` everything for `k ≥ 1`.
`exists_nontrivial_mack_model` states that there is a probability space, a random triangle with
three accident years, and constants `f`, `σ²` with `0 < σ² 0` satisfying `Mack1`, `Mack3` and
`Mack2'`, with two outcomes giving different `C_{0,1}`. Here `σ_0² = 4`.
`fhat0_unbiased`, `ultimate_unbiased`, `var_fhat0` and `sigma2_unbiased` instantiate Theorem 2,
Theorem 1, the estimation variance and the unbiasedness of `σ̂²` on it, every hypothesis discharged.

**Gap.** Not in any source. It is what makes the conditional statements non-vacuous: `f̂_0` is
genuinely random and its conditional expectation is still `2`.

### Independent rows and the row-generated filtration

**Lean.** `IndependenceWitness.X` is the same eight-outcome triangle equipped with the filtration
`Dgen k = ⨆ i, ⨆ j, ⨆ _ : j ≤ k, comap (Cw i j)`, so `rowsGenerateD` holds by construction.
`rowsIndep` proves `RowsIndep X μ` from the independence of the three shock events.
`mack1Row` proves `Mack1Row X μ f`. `mack1_from_rows` and `mack2'_from_rows` are the derived `D_k`
statements obtained by applying `mack1_of_mack1Row` and `mack2'_of_rows`.
`exists_independence_witness` packages all of it with the nondegeneracy of `C_{0,1}`.
The module docstring names these as the finite-model forms of Mack (1993) eq. (1) and (2) and of the
`B_k` filtration used in the proof of Theorem 2, pp. 214-216.

**Gap.** Not in any source. It closes the loop on `RowsGenerateD` and `RowsIndep`, which are
hypotheses everywhere else in the library.

### The cross-term condition of the total

**Lean.** `NontrivialModel.crossFree_ultimates` proves
`CondCrossFree μ (Dfil 0) (range 3) (fun i => X.C i 2)`, and `ultimate_nontrivial` shows the
ultimate takes two different values, so `exists_crossFree_nondegenerate` gives both together.

**Gap.** Not in any source. It shows that `CondCrossFree`, which `condMsepTotal_eq` assumes rather
than derives, is satisfiable by genuinely random ultimates.

## Hypotheses still assumed rather than derived

Ordered roughly by how much they matter.

1. **`hfut1` and `hfut2`, "the observed data adds nothing about this row's future".** Taken as
   hypotheses by `condMsep_eq`, `condVar_ultimate_eq_procVar`, `condExp_ultimate_of_Mack1`,
   `condMsepTotal_eq` and `sum_procVar_le_condMsepTotal`, and DERIVED from independence in
   `ObservedData.lean`: `condExp_obsSigma_eq_D` supplies them on the observed-data σ-algebra
   `obsSigma`, and `condMsep_eq_of_rows` states Theorem 3 in exact form from `Mack1Row`,
   `Mack3Row`, `RowsIndep`, `RowsGenerateD` and square integrability alone. What remains
   assumed is only the modelling input (`RowsGenerateD`, item 4) and integrability (item 6).
2. **`CondCrossFree`, the cross-term condition across accident years.** Taken as a hypothesis by
   `condMsepTotal_eq` and `sum_procVar_le_condMsepTotal`, and DERIVED from `RowsIndep` by
   `condCrossFree_of_rows`; `condMsepTotal_eq_of_rows` is the total-reserve form from the
   row-conditioned assumptions and independence. Also witnessed by
   `NontrivialModel.crossFree_ultimates` and `IndependenceWitness.condCrossFree_obs_of_rows`.
3. **`Mack2'`.** Assumed in `condExp_sq_fhatRv_sub`, `condExp_wssRv` and `condExp_sigma2Rv`, even
   though `mack2'_of_rows` derives it from `RowsIndep`, `RowsGenerateD` and `Mack1Row`. A caller
   must apply the derivation explicitly.
4. **`RowsGenerateD`.** Assumed in `mack1_of_mack1Row`, `mack3_of_mack3Row` and `mack2'_of_rows`.
   The `RandomTriangle` structure does not force the filtration to be the join of the rows'
   histories, so this must be supplied; `IndependenceWitness.rowsGenerateD` supplies it on the
   witness by construction.
5. **`Mack1Row` and `Mack3Row`, and their `D_k` forms `Mack1` and `Mack3`.** These are the model,
   so they are assumptions by nature. Recorded here because the row form and the `D_k` form are
   different hypotheses and the theorems mix them: `mack2'_of_rows` consumes the row form while the
   variance theorems consume the `D_k` form.
6. **Integrability, everywhere.** `hCint`, `hfint`, `hprod`, `hC`, `hCsq`, `hε`, `hε2`, `hCε`,
   `hεC`, `hsq`, `hSsq` in `condExp_fhatRv`, `condExp_fhatRv_mul`, `integral_fhatRv`,
   `integral_fhatRv_mul`, `condExp_ChatRv`, `condExp_ultimate_eq`, `condExp_sq_fhatRv_sub`,
   `condExp_wssRv`, `condExp_sigma2Rv`, `condExp_sq_C_succ`, `condExp_sq_C_succ_tower`,
   `condVar_C_eq_procVar`, `condMsep_eq`, `mack1_of_mack1Row`, `mack3_of_mack3Row`,
   `mack2'_of_rows`, `condExp_fhatWrv`, `condExp_sq_fhatWrv_sub`, `condExp_wssWrv` and
   `condExp_sigma2Wrv`. In `TotalMsep.lean` these are replaced by `MemLp _ 2 μ`
   hypotheses (`hPmem`, `hCmem`), from which Hölder supplies the products. Nothing derives any of
   them from a moment condition on the model.
7. **Almost-sure nonvanishing of the column sums.** `hS : ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0` in
   `condExp_fhatRv`, `condExp_fhatRv_mul`, `integral_fhatRv`, `integral_fhatRv_mul`,
   `condExp_sq_fhatRv_sub`, `condExp_wssRv`, `condExp_sigma2Rv`, and in the quantified form
   `∀ k, k + 2 ≤ n → ...` in `condExp_ChatRv` and `condExp_ultimate_eq`. The weighted analogue is
   `hS : ∀ᵐ ω, X.SWrv w α k ω ≠ 0` in `condExp_fhatWrv`,
   `condExp_sq_fhatWrv_sub`, `condExp_wssWrv` and `condExp_sigma2Wrv`.
8. **Almost-sure nonvanishing of the individual entries.** `hC : ∀ i ∈ contributors n k, ∀ᵐ ω, X.C i k ω ≠ 0`
   in `condExp_wssRv` and `condExp_sigma2Rv`, `hC0` in `condExp_fhatWrv`, and `hC` in the weighted
   variance theorems. Those weighted theorems also require every `weightVolume w α i k` to be
   almost surely nonzero. The deterministic
   counterpart is `h : ∀ i ∈ contributors n k, C i k ≠ 0` in `fhat_eq_weighted_average`,
   `T_eq_sum_weighted_F`, `weighted_sq_dev`, `weighted_sq_dev_at_fhat`, `weighted_sq_dev_eps`,
   `TW_unit`, `fhatW_unit`, `sigma2W_unit`, `ChatW_unit`, `ultimateW_unit`, `mackTermW_unit`,
   `msepW_unit`, `se2recW_unit` and `se2recW_eq_msep_unit`.
9. **Nonzero development factors and projections along the row.** `hf` in `se2rec_eq_closed`,
   `se2rec_eq_msep`, `se2recW_eq_closed`, `se2recW_eq_msepW`, `rohrProcess_eq_mackProcess`,
   `msep_eq_mackProcess_add_mackEstimation`, `rohrMsep_eq_mackProcess_add_mackEstimation`,
   `CLcum_eq_ultimate_div`, `sum_CLcum_obsCol`, `sum_CLcum_contributors`,
   `chainLadder_fitted_column_totals` and `chainLadder_scoreEquations`; `hChat` alongside it in
   `msep_eq_mackProcess_add_mackEstimation_of_lt` and
   `msepTotal_eq_sum_mackProcess_add_mackTotalEstimation`; `hS` in `weighted_sq_dev_at_fhat`,
   `weighted_sq_devW_at_fhatW` and `weighted_sq_dev_eps`; `h : cdf C n i ≠ 0` in
   `bfUltimate_of_ultimate` and `bfReserve_of_ultimate`; `hU : ultimate C n i ≠ 0` in
   `msep_div_ultimate_sq`.
10. **Nonnegativity.** `ha : ∀ k ∈ Ico (n-1-i) (n-1), 0 ≤ relVar C n k` in
    `mackEstimation_le_bbmwEstimation`, `bbmwEstimation_sub_mackEstimation_le`,
    `rohrParameter_le_bbmwEstimation` and `rowProd_sub_rowSum_nonneg`; the stronger
    `ha : ∀ k, 0 ≤ relVar C n k` together with `hU : ∀ i ∈ range n, 0 ≤ ultimate C n i` in
    `mackTotalEstimation_le_bbmwTotalEstimation`; `hU : 0 ≤ U` and `hf : ∀ k ∈ row, 1 ≤ fhat C n k`
    in `bfReserve_nonneg` and `bfReserve_le`. Nothing derives `0 ≤ relVar C n k` from
    nonnegativity of the triangle entries, which the library never assumes.
11. **Positivity of the multiplicative parameters.** `ha : ∀ j < n, 0 < a j` and
    `hb : ∀ j < n, 0 < b j`, with `PatternNormalized b n`, in `patternCum_mul_fhat`,
    `patternCum_mul_prod`, `fhat_pos_of_mult`, `mult_cum_eq_CLcum` and `multFit_eq_CLincr`.
12. **Measurability of the predictor and of the weights.** `hPmeas : StronglyMeasurable[D] (X.ChatRv i m)`
    in `condMsep_eq` and `condMsepTotal_eq`; `hw : ∀ i, StronglyMeasurable[X.D k] (w i k)` in
    `condExp_fhatWrv`, `condExp_sq_fhatWrv_sub`, `condExp_wssWrv`, `condExp_sigma2Wrv`,
    `RandomTriangle.stronglyMeasurable_SWrv`, `RandomTriangle.stronglyMeasurable_gW` and
    `RandomTriangle.stronglyMeasurable_weightVolume`.
13. **Finiteness of the measure.** `IsFiniteMeasure μ` in most stochastic theorems and
    `IsProbabilityMeasure μ` in `integral_fhatRv` and `integral_fhatRv_mul`. `condExp_fhatRv` and
    `condExp_fhatWrv` need neither.
