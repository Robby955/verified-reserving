import VerifiedReserving.CDR
import VerifiedReserving.TotalReserve

/-!
# Merz-Wüthrich (2008): the mean squared error of prediction of the one-year
# claims development result

`CDR.lean` defines the true one-year claims development result and proves the
two exact statements about it (conditional mean zero, and the closed form
`CDR_i(k) = (∏_{j>k} f_j)(f_k C_{i,k} - C_{i,k+1})` under (M1)). This file adds
the second moment: the conditional mean squared error of prediction of the CDR
when it is predicted by zero, which is what a Solvency II one-year reserve risk
figure reports.

The discipline is the one the library uses for Mack. The exact object is a
theorem; the published estimator is a definition, stated exactly as the paper
displays it, and the two are connected by deterministic bridge theorems.

## Source

Merz and Wüthrich, *Modelling the claims development result for solvency
purposes*, Casualty Actuarial Society E-Forum, Fall 2008, pages 542-568. The
displays formalized below were read from that paper: (2.18) for the exact
conditional variance of the true CDR, (3.4)-(3.7) for the estimator's building
blocks `Δ̂`, `Φ̂`, `Ψ̂`, `Γ̂`, (3.8)-(3.10) for the single-accident-year
estimators, (3.17) for the collapsed single-accident-year display, and
(3.12)-(3.16) for the aggregation over accident years. The same formulas are
what R's `ChainLadder` package computes in `CDR.MackChainLadder`.

## Index conventions

The paper writes `I` for the last accident year, `J = I` for the last
development year, and `D_I` for the triangle after `I` diagonals. This library
writes `n` for the number of accident years, so `I = J = n - 1`, accident and
development years are zero-based, and `C_{i,k}` is observed when `i + k ≤ n-1`.
The dictionary is

* `I - i`, the latest observed development year of accident year `i`, is `n-1-i`;
* `C_{I-j,j}`, the newest observed cell of column `j`, is `C (n-1-j) j`;
* `S^I_j = ∑_{i=0}^{I-j-1} C_{i,j}` is `S C n j`, and the same column sum one
  year later, `S^{I+1}_j = ∑_{i=0}^{I-j} C_{i,j}`, is `S C (n+1) j`. Both are
  computable from the triangle observed today: `S_succ_eq` proves
  `S^{I+1}_j = S^I_j + C_{I-j,j}`, the newest cell of column `j` being on the
  latest observed diagonal;
* `f̂^I_j` is `fhat C n j`, `σ̂²_j` is `sigma2 C n j` (the paper's (3.3) is this
  library's `sigma2`, division by `I-j-1 = n-j-2` included), and `Ĉ^I_{i,J}` is
  `ultimate C n i`.

## Filtration

Every stochastic statement below is in the filtration carried by
`RandomTriangle`: `D k` is everything observed up to development year `k`, for
all accident years. That is the filtration in which (M1) and (M3) are assumed
here. Merz and Wüthrich index information by calendar year, `D_I` being the
triangle after `I` diagonals, and their one-year step is `D_I → D_{I+1}`. The
step formalized here is the development-year step `D_k → D_{k+1}`, the same
caveat `CDR.lean` records for `trueCDR_eq`: the martingale property holds in
either filtration, and the closed forms are stated in the filtration (M1) is
assumed in.

## What is proved

* `condExp_sq_trueCDR`: the exact layer. Under (M1) and (M3),
  `E[CDR_i(k)² | D_k] = (∏_{j>k} f_j)² σ_k² C_{i,k}` almost surely. Since the
  true CDR has conditional mean zero (`condExp_trueCDR_eq_zero`), this second
  moment is its conditional variance, and predicting the CDR by zero has
  exactly this conditional mean squared error. It is display (2.18) of the
  paper, `Var(CDR_i(I+1) | D_I) = E[C_{i,J} | D_I]² (σ²_{I-i}/f²_{I-i})/C_{i,I-i}`,
  written with the product split off instead of divided out.
* `condVar_trueCDR`: the same quantity as a conditional variance.
* `mwPsi`, `mwPhi`, `mwGamma`, `mwDelta` and the estimators `mwVarCDR`,
  `mwProcessCDR`, `mwParamCDR`, `mwMsepCDR`, `mwMsepObsCDR`: the paper's
  (3.4)-(3.10) as definitions.
* `mwMsepCDR_eq_display`: those definitions collapse to the paper's own
  display (3.17), where the remaining run-off cells appear scaled by
  `C_{I-j,j}/S^{I+1}_j ≤ 1`. This is the identity that makes Merz-Wüthrich
  readable next to Mack, and it holds because `S^{I+1}_j = S^I_j + C_{I-j,j}`.
* `mwVarCDR_eq_plugin` and `mwProcessCDR_eq_plugin`: the bridge. The paper's
  estimator of the first development step is exactly the plug-in of the exact
  expression above, `Ĉ_{i,k}` playing the part of `C_{i,k}` and `f̂, σ̂²` the
  parts of `f, σ²`; the rest of `mwProcessCDR` is the correction `Φ̂` for the
  later steps.
* `sum_procVar_step_eq_procVar`: the one-year process variances telescope. The
  exact one-year quantity of `condExp_sq_trueCDR`, summed over every remaining
  development step of the row with `C_{i,k}` replaced by its (M1) prediction
  `C_{i,d} ∏_{l<k} f_l`, is Mack's multi-year process variance `procVar`
  exactly, with no remainder. `condExp_sum_cdrProcVar_eq_procVar` is the same
  statement with the replacement performed by a conditional expectation
  instead of by hand.
* `mwLambda`, `mwXi`, `mwCross`, `mwCrossObs`, `mwMsepTotalCDR`,
  `mwMsepTotalObsCDR`: the aggregation over accident years, (3.12)-(3.15), as
  definitions, and `mwMsepTotalCDR_sub_mwMsepTotalObsCDR`, the paper's
  decoupling (3.16).

Nothing here upgrades an estimator to an identity. The passage from the exact
conditional MSEP to `mwMsepCDR` uses the linear approximation of the paper's
appendix (A.1), in which the estimated development factors are treated as
resampled ones and terms of higher order in the residuals are dropped; that
step is not formalized, which is why every `mw*` object is a definition.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

/-! ## The exact one-year process variance -/

/-- The one-year process variance of the true claims development result of a
row sitting at claims `c` in development year `k`, with ultimate development
year `N`:
`(∏_{j ∈ [k+1, N)} f_j)² σ_k² c`.
For `N = n-1` this is the right-hand side of `condExp_sq_trueCDR`, that is,
Merz-Wüthrich (2008) display (2.18) with the product written out rather than
divided out of `E[C_{i,J} | D_I]²`. -/
def cdrProcVar (c : ℝ) (f σ2 : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (∏ j ∈ Ico (k + 1) N, f j) ^ 2 * (σ2 k * c)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- **Merz-Wüthrich (2008), display (2.18): the conditional MSEP of the true
one-year claims development result predicted by zero.** Under (M1) and (M3),
for `i < n` and `k < n-1`,
`E[CDR_i(k)² | D_k] = (∏_{j ∈ [k+1, n-1)} f_j)² σ_k² C_{i,k}` almost surely.

The whole one-year move of the predicted ultimate is `(∏_{j>k} f_j)` times the
one-step residual `f_k C_{i,k} - C_{i,k+1}` (`trueCDR_eq`), so its conditional
second moment is that factor squared times `E[ε_{i,k}² | D_k] = σ_k² C_{i,k}`,
which is assumption (M3). Because the true CDR has conditional mean zero
(`condExp_trueCDR_eq_zero`), this is at once the conditional variance of the
true CDR and the conditional mean squared error of predicting it by zero: the
budget value the paper puts in the income statement for prior accident years.

The step is the development-year step `D_k → D_{k+1}` of this library's
filtration, not the paper's calendar-year step; see the module docstring. -/
theorem condExp_sq_trueCDR [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f σ2 : ℕ → ℝ)
    (i k : ℕ) (hi : i < n) (hk : k < n - 1) (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hint : ∀ j, Integrable (X.C i j) μ) :
    μ[fun ω => (X.trueCDR μ i k ω) ^ 2 | X.D k]
      =ᵐ[μ] fun ω => cdrProcVar (X.C i k ω) f σ2 (n - 1) k := by
  have hCDR := trueCDR_eq X f i k hi hk hM hint
  have hsq : (fun ω => (X.trueCDR μ i k ω) ^ 2)
      =ᵐ[μ] ((∏ j ∈ Ico (k + 1) (n - 1), f j) ^ 2) • fun ω => (X.eps f i k ω) ^ 2 := by
    filter_upwards [hCDR] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul, RandomTriangle.eps, hω]
    ring
  refine (condExp_congr_ae hsq).trans ((condExp_smul _ _ _).trans ?_)
  filter_upwards [h3 i hi k] with ω hω
  simp only [Pi.smul_apply, smul_eq_mul, hω, cdrProcVar]

/-- The same quantity read as a conditional variance. The true CDR has
conditional mean zero, so its conditional variance given `D_k` is its
conditional second moment, `(∏_{j>k} f_j)² σ_k² C_{i,k}`. -/
theorem condVar_trueCDR [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f σ2 : ℕ → ℝ)
    (i k : ℕ) (hi : i < n) (hk : k < n - 1) (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hint : ∀ j, Integrable (X.C i j) μ) :
    (fun ω => (μ[fun ω => (X.trueCDR μ i k ω) ^ 2 | X.D k]) ω
        - ((μ[X.trueCDR μ i k | X.D k]) ω) ^ 2)
      =ᵐ[μ] fun ω => cdrProcVar (X.C i k ω) f σ2 (n - 1) k := by
  filter_upwards [condExp_sq_trueCDR X f σ2 i k hi hk hM h3 hint,
    condExp_trueCDR_eq_zero (μ := μ) X i k] with ω h1 h2
  simp [h1, h2]

end

/-! ## The Merz-Wüthrich estimator, deterministic layer

Definitions only, exactly as the paper displays them. -/

noncomputable section Estimator

open Finset

/-- The column sum one year later. `S^{I+1}_j = S^I_j + C_{I-j,j}`: the extra
contributor to column `j` on the next diagonal is the cell `C_{I-j,j}`, which
is already observed today. Every `S^{I+1}_j` appearing in the Merz-Wüthrich
estimator is therefore a function of the triangle at time `I`. -/
theorem S_succ_eq (C : ℕ → ℕ → ℝ) (n j : ℕ) (hj : j < n) :
    S C (n + 1) j = S C n j + C (n - 1 - j) j := by
  have h : n + 1 - j - 1 = (n - j - 1) + 1 := by omega
  have h3 : C (n - j - 1) j = C (n - 1 - j) j := by
    rw [show n - j - 1 = n - 1 - j from by omega]
  rw [S, S, contributors, contributors, h, Finset.sum_range_succ, h3]

/-- Merz-Wüthrich (2008), display (3.6):
`Ψ̂^I_i = (σ̂²_{I-i}/(f̂^I_{I-i})²) / C_{i,I-i}`.
The relative uncertainty of the single development step that the next calendar
year actually observes for accident year `i`. -/
def mwPsi (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  sigma2 C n (n - 1 - i) / (fhat C n (n - 1 - i)) ^ 2 / C i (n - 1 - i)

/-- Merz-Wüthrich (2008), display (3.5):
`Φ̂^I_{i,J} = ∑_{j=I-i+1}^{J-1} (C_{I-j,j}/S^{I+1}_j)² (σ̂²_j/(f̂^I_j)²) / C_{I-j,j}`.
The remaining run-off steps enter the one-year uncertainty only through the
re-estimation of their development factors on the next diagonal, which is why
each is scaled by `(C_{I-j,j}/S^{I+1}_j)² ≤ 1`. -/
def mwPhi (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  ∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
    (C (n - 1 - j) j / S C (n + 1) j) ^ 2 * (sigma2 C n j / (fhat C n j) ^ 2) / C (n - 1 - j) j

/-- Merz-Wüthrich (2008), display (3.7): `Γ̂^I_{i,J} = Φ̂^I_{i,J} + Ψ̂^I_i`. -/
def mwGamma (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := mwPhi C n i + mwPsi C n i

/-- Merz-Wüthrich (2008), display (3.4):
`Δ̂^I_{i,J} = (σ̂²_{I-i}/(f̂^I_{I-i})²)/S^I_{I-i}
  + ∑_{j=I-i+1}^{J-1} (C_{I-j,j}/S^{I+1}_j)² (σ̂²_j/(f̂^I_j)²)/S^I_j`,
the parameter-estimation part of the one-year uncertainty. -/
def mwDelta (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  sigma2 C n (n - 1 - i) / (fhat C n (n - 1 - i)) ^ 2 / S C n (n - 1 - i)
    + ∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
        (C (n - 1 - j) j / S C (n + 1) j) ^ 2 * (sigma2 C n j / (fhat C n j) ^ 2) / S C n j

/-- Merz-Wüthrich (2008), display (3.8): the estimator of the conditional
variance of the true CDR, `V̂ar(CDR_i(I+1) | D_I) = (Ĉ^I_{i,J})² Ψ̂^I_i`. This is
the plug-in of the exact `condExp_sq_trueCDR`; `mwVarCDR_eq_plugin` proves it. -/
def mwVarCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := (ultimate C n i) ^ 2 * mwPsi C n i

/-- The process part of Merz-Wüthrich (2008), display (3.9):
`(Ĉ^I_{i,J})² Γ̂^I_{i,J}`, the first development step (`Ψ̂`) together with the
correction `Φ̂` for the later steps. -/
def mwProcessCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := (ultimate C n i) ^ 2 * mwGamma C n i

/-- The parameter-error part of Merz-Wüthrich (2008), display (3.9):
`(Ĉ^I_{i,J})² Δ̂^I_{i,J}`. -/
def mwParamCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := (ultimate C n i) ^ 2 * mwDelta C n i

/-- **Merz-Wüthrich (2008), display (3.9).** Their estimator of the conditional
mean squared error of prediction of the observable claims development result of
accident year `i` around the budget value zero:
`msêp_{ĈDR_i(I+1)|D_I}(0) = (Ĉ^I_{i,J})² (Γ̂^I_{i,J} + Δ̂^I_{i,J})`.
A definition, not a theorem: the derivation in the paper's appendix replaces
the estimated development factors by resampled ones and drops terms of higher
order in the residuals. -/
def mwMsepCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := mwProcessCDR C n i + mwParamCDR C n i

/-- **Merz-Wüthrich (2008), display (3.10).** The retrospective view: the
estimator of the conditional MSEP of the observable CDR around the true CDR,
`(Ĉ^I_{i,J})² (Φ̂^I_{i,J} + Δ̂^I_{i,J})`. -/
def mwMsepObsCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 * (mwPhi C n i + mwDelta C n i)

/-! ### The relations among the displayed estimators -/

/-- **Merz-Wüthrich (2008), first line of display (3.11).** The prospective
estimator exceeds the retrospective one by exactly the estimated variance of
the true CDR: `msêp(0) = msêp(ĈDR) + V̂ar(CDR | D_I)`. Algebra on the
definitions, since `Γ̂ = Φ̂ + Ψ̂`. -/
theorem mwMsepCDR_eq_mwMsepObsCDR_add_mwVarCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    mwMsepCDR C n i = mwMsepObsCDR C n i + mwVarCDR C n i := by
  simp only [mwMsepCDR, mwMsepObsCDR, mwVarCDR, mwProcessCDR, mwParamCDR, mwGamma]
  ring

/-- **Merz-Wüthrich (2008), second line of display (3.11).** With a nonnegative
`Ψ̂` (which holds whenever the triangle entries and `σ̂²` are nonnegative), the
retrospective estimator is at most the prospective one. -/
theorem mwMsepObsCDR_le_mwMsepCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) (h : 0 ≤ mwPsi C n i) :
    mwMsepObsCDR C n i ≤ mwMsepCDR C n i := by
  rw [mwMsepCDR_eq_mwMsepObsCDR_add_mwVarCDR]
  have : 0 ≤ mwVarCDR C n i := mul_nonneg (sq_nonneg _) h
  linarith

/-- The per-column collapse behind display (3.17): with `s' = s + c`,
`(c/s')² a / c + (c/s')² a / s = (c/s') a / s`. -/
theorem mw_term_split (a c s : ℝ) (hs : s ≠ 0) (hsc : s + c ≠ 0) :
    (c / (s + c)) ^ 2 * a / c + (c / (s + c)) ^ 2 * a / s = c / (s + c) * a / s := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · field_simp

/-- **Merz-Wüthrich (2008), display (3.17).** The single-accident-year estimator
written out:
`msêp_{ĈDR_i(I+1)|D_I}(0) = (Ĉ^I_{i,J})² ( (σ̂²_{I-i}/(f̂^I_{I-i})²)/C_{i,I-i}
  + (σ̂²_{I-i}/(f̂^I_{I-i})²)/S^I_{I-i}
  + ∑_{j=I-i+1}^{J-1} (C_{I-j,j}/S^{I+1}_j)(σ̂²_j/(f̂^I_j)²)/S^I_j )`.
Compared with Mack's Theorem 3 the one-year figure keeps only the first term of
the process variance, keeps the estimation error of the next diagonal in full,
and scales every remaining run-off cell by `C_{I-j,j}/S^{I+1}_j ≤ 1`. The
collapse of the two sums into one is exactly `S^{I+1}_j = S^I_j + C_{I-j,j}`
(`S_succ_eq`); the hypotheses are that the two column sums involved do not
vanish. -/
theorem mwMsepCDR_eq_display (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (hS : ∀ j ∈ Ico (n - 1 - i + 1) (n - 1), S C n j ≠ 0)
    (hS' : ∀ j ∈ Ico (n - 1 - i + 1) (n - 1), S C (n + 1) j ≠ 0) :
    mwMsepCDR C n i
      = (ultimate C n i) ^ 2 *
          (sigma2 C n (n - 1 - i) / (fhat C n (n - 1 - i)) ^ 2 / C i (n - 1 - i)
            + sigma2 C n (n - 1 - i) / (fhat C n (n - 1 - i)) ^ 2 / S C n (n - 1 - i)
            + ∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
                C (n - 1 - j) j / S C (n + 1) j
                  * (sigma2 C n j / (fhat C n j) ^ 2) / S C n j) := by
  have hsum :
      (∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
          (C (n - 1 - j) j / S C (n + 1) j) ^ 2 * (sigma2 C n j / (fhat C n j) ^ 2)
            / C (n - 1 - j) j)
        + (∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
            (C (n - 1 - j) j / S C (n + 1) j) ^ 2 * (sigma2 C n j / (fhat C n j) ^ 2)
              / S C n j)
      = ∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
          C (n - 1 - j) j / S C (n + 1) j * (sigma2 C n j / (fhat C n j) ^ 2) / S C n j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hjn : j < n := by have := (mem_Ico.mp hj).2; omega
    have hSj := hS j hj
    have hSj' := hS' j hj
    rw [S_succ_eq C n j hjn] at hSj' ⊢
    exact mw_term_split _ _ _ hSj hSj'
  rw [← hsum]
  simp only [mwMsepCDR, mwProcessCDR, mwParamCDR, mwGamma, mwPhi, mwPsi, mwDelta]
  ring

/-! ### The bridge to the exact one-year process variance -/

/-- **The Merz-Wüthrich estimator of the first development step is the plug-in
of the exact expression.** `V̂ar(CDR_i(I+1) | D_I) = (Ĉ^I_{i,J})² Ψ̂^I_i` of
display (3.8) is `cdrProcVar` with `C_{i,I-i}` for the claims and `f̂, σ̂²` for
the model parameters, that is, the right-hand side of `condExp_sq_trueCDR` with
the estimators substituted. The hypotheses are that the row is not already
fully developed and that the development factor and the claims at the latest
observed cell do not vanish. -/
theorem mwVarCDR_eq_plugin (C : ℕ → ℕ → ℝ) (n i : ℕ) (hd : n - 1 - i < n - 1)
    (hf : fhat C n (n - 1 - i) ≠ 0) (hC : C i (n - 1 - i) ≠ 0) :
    mwVarCDR C n i
      = cdrProcVar (C i (n - 1 - i)) (fhat C n) (sigma2 C n) (n - 1) (n - 1 - i) := by
  have hU : ultimate C n i
      = C i (n - 1 - i)
          * (fhat C n (n - 1 - i) * ∏ j ∈ Ico (n - 1 - i + 1) (n - 1), fhat C n j) := by
    rw [ultimate, Chat, Finset.prod_eq_prod_Ico_succ_bot hd]
  simp only [mwVarCDR, mwPsi, cdrProcVar]
  rw [hU]
  field_simp

/-- **The process part of the Merz-Wüthrich estimator, split at the first
development step.** `(Ĉ^I_{i,J})² Γ̂^I_{i,J}` is the plug-in of the exact
one-year process variance of `condExp_sq_trueCDR` for the step the next
calendar year observes, plus the correction `(Ĉ^I_{i,J})² Φ̂^I_{i,J}` carried by
the re-estimation of the later development factors. -/
theorem mwProcessCDR_eq_plugin (C : ℕ → ℕ → ℝ) (n i : ℕ) (hd : n - 1 - i < n - 1)
    (hf : fhat C n (n - 1 - i) ≠ 0) (hC : C i (n - 1 - i) ≠ 0) :
    mwProcessCDR C n i
      = cdrProcVar (C i (n - 1 - i)) (fhat C n) (sigma2 C n) (n - 1) (n - 1 - i)
          + (ultimate C n i) ^ 2 * mwPhi C n i := by
  have h := mwVarCDR_eq_plugin C n i hd hf hC
  rw [mwVarCDR] at h
  simp only [mwProcessCDR, mwGamma]
  rw [mul_add, h]
  ring

/-! ### Telescoping: the one-year process variances over the run-off -/

/-- The one-year process variances of the successive development steps, with the
claims at step `d + j` replaced by their (M1) prediction
`c ∏_{l ∈ [d, d+j)} f_l`, sum to Mack's multi-year process variance `procVar`.
Term by term this is `procVar_eq_sum`: the `j`-th summand of the closed form of
`procVar` is the one-year process variance of step `d + j`. -/
theorem sum_range_cdrProcVar_eq_procVar (c : ℝ) (f σ2 : ℕ → ℝ) (d m : ℕ) :
    ∑ j ∈ range m, cdrProcVar (c * ∏ l ∈ Ico d (d + j), f l) f σ2 (d + m) (d + j)
      = procVar c f σ2 d m := by
  rw [procVar_eq_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [cdrProcVar]

/-- **The one-year process variances telescope into Mack's process variance,
exactly.** Summing the exact one-year quantity of `condExp_sq_trueCDR` over
every remaining development step `k` of the row, with `C_{i,k}` replaced by its
(M1) prediction `c ∏_{l ∈ [d,k)} f_l`, returns Mack's multi-year process
variance `procVar c f σ² d m` with no remainder. The one-year view and the
run-off view of process risk differ only in what is held fixed, not in total. -/
theorem sum_procVar_step_eq_procVar (c : ℝ) (f σ2 : ℕ → ℝ) (d m : ℕ) :
    ∑ k ∈ Ico d (d + m), cdrProcVar (c * ∏ l ∈ Ico d k, f l) f σ2 (d + m) k
      = procVar c f σ2 d m := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  exact sum_range_cdrProcVar_eq_procVar c f σ2 d m

end Estimator

noncomputable section Telescope

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- The stochastic form of the telescoping identity. Under (M1), the sum over
the remaining development steps of the conditional expectations given `D_d` of
the exact one-year process variances is Mack's process variance `procVar` at
the claims `C_{i,d}` observed today. The substitution performed by hand in
`sum_procVar_step_eq_procVar` is here performed by the conditional
expectation: `E[C_{i,d+j} | D_d] = C_{i,d} ∏_{l ∈ [d,d+j)} f_l`. -/
theorem condExp_sum_cdrProcVar_eq_procVar [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (f σ2 : ℕ → ℝ) (i d m : ℕ) (hi : i < n) (hM : Mack1 X μ f)
    (hint : ∀ j, Integrable (X.C i j) μ) :
    (fun ω => ∑ j ∈ range m,
        (μ[fun ω => cdrProcVar (X.C i (d + j) ω) f σ2 (d + m) (d + j) | X.D d]) ω)
      =ᵐ[μ] fun ω => procVar (X.C i d ω) f σ2 d m := by
  have key : ∀ j ∈ range m,
      μ[fun ω => cdrProcVar (X.C i (d + j) ω) f σ2 (d + m) (d + j) | X.D d]
        =ᵐ[μ] fun ω =>
          cdrProcVar (X.C i d ω * ∏ l ∈ Ico d (d + j), f l) f σ2 (d + m) (d + j) := by
    intro j _
    have hA : (fun ω => cdrProcVar (X.C i (d + j) ω) f σ2 (d + m) (d + j))
        = ((∏ l ∈ Ico (d + j + 1) (d + m), f l) ^ 2 * σ2 (d + j)) • X.C i (d + j) := by
      ext ω
      simp only [cdrProcVar, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hA]
    refine (condExp_smul _ _ _).trans ?_
    filter_upwards [condExp_C_of_Mack1_at X f i d j hi hM hint] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul, hω, cdrProcVar]
    ring
  have hall : ∀ᵐ ω ∂μ, ∀ j ∈ range m,
      (μ[fun ω => cdrProcVar (X.C i (d + j) ω) f σ2 (d + m) (d + j) | X.D d]) ω
        = cdrProcVar (X.C i d ω * ∏ l ∈ Ico d (d + j), f l) f σ2 (d + m) (d + j) := by
    rw [eventually_all_finset]
    exact key
  filter_upwards [hall] with ω hω
  rw [Finset.sum_congr rfl fun j hj => hω j hj]
  exact sum_range_cdrProcVar_eq_procVar _ f σ2 d m

end Telescope

/-! ## Aggregation over accident years

Merz-Wüthrich (2008), Section 3.2. Accident year `0` is fully developed and
contributes nothing, so the sums run over `i = 1, …, n-1`, and the cross terms
run over the pairs `k > i > 0` with the older year `i` carrying the shared
development factors. Definitions only. -/

noncomputable section Aggregate

open Finset

/-- Merz-Wüthrich (2008), display (3.13):
`Λ̂^I_{i,J} = (C_{i,I-i}/S^{I+1}_{I-i})(σ̂²_{I-i}/(f̂^I_{I-i})²)/S^I_{I-i}
  + ∑_{j=I-i+1}^{J-1} (C_{I-j,j}/S^{I+1}_j)² (σ̂²_j/(f̂^I_j)²)/S^I_j`,
the cross-term counterpart of `Δ̂`. -/
def mwLambda (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  C i (n - 1 - i) / S C (n + 1) (n - 1 - i)
      * (sigma2 C n (n - 1 - i) / (fhat C n (n - 1 - i)) ^ 2) / S C n (n - 1 - i)
    + ∑ j ∈ Ico (n - 1 - i + 1) (n - 1),
        (C (n - 1 - j) j / S C (n + 1) j) ^ 2 * (sigma2 C n j / (fhat C n j) ^ 2) / S C n j

/-- Merz-Wüthrich (2008), display (3.14):
`Ξ̂^I_{i,J} = Φ̂^I_{i,J} + (σ̂²_{I-i}/(f̂^I_{I-i})²)/S^{I+1}_{I-i} ≥ Φ̂^I_{i,J}`. -/
def mwXi (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  mwPhi C n i + sigma2 C n (n - 1 - i) / (fhat C n (n - 1 - i)) ^ 2 / S C (n + 1) (n - 1 - i)

/-- The cross term of accident year `i` against every younger accident year in
Merz-Wüthrich (2008), display (3.12): `2 Ĉ^I_{i,J} (∑_{k>i} Ĉ^I_{k,J}) (Φ̂^I_{i,J} + Λ̂^I_{i,J})`. -/
def mwCrossObs (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  2 * (ultimate C n i * laterUltimates C n i) * (mwPhi C n i + mwLambda C n i)

/-- The cross term of accident year `i` in Merz-Wüthrich (2008), display
(3.15): `2 Ĉ^I_{i,J} (∑_{k>i} Ĉ^I_{k,J}) (Ξ̂^I_{i,J} + Λ̂^I_{i,J})`. -/
def mwCross (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  2 * (ultimate C n i * laterUltimates C n i) * (mwXi C n i + mwLambda C n i)

/-- **Merz-Wüthrich (2008), display (3.12).** The retrospective estimator for
the aggregated observable claims development result. -/
def mwMsepTotalObsCDR (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 n, mwMsepObsCDR C n i + ∑ i ∈ Ico 1 n, mwCrossObs C n i

/-- **Merz-Wüthrich (2008), display (3.15).** The prospective estimator for the
aggregated observable claims development result around zero, the figure a
Solvency II one-year reserve risk calculation reports. -/
def mwMsepTotalCDR (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 n, mwMsepCDR C n i + ∑ i ∈ Ico 1 n, mwCross C n i

/-- **Merz-Wüthrich (2008), display (3.16): the same decoupling for aggregated
accident years as for a single one.** The prospective aggregate exceeds the
retrospective aggregate by the summed estimated variances of the true CDRs plus
the cross terms `2 Ĉ_i (∑_{k>i} Ĉ_k)(Ξ̂_i - Φ̂_i)`. Algebra on the definitions
and the single-year display (3.11). -/
theorem mwMsepTotalCDR_sub_mwMsepTotalObsCDR (C : ℕ → ℕ → ℝ) (n : ℕ) :
    mwMsepTotalCDR C n - mwMsepTotalObsCDR C n
      = ∑ i ∈ Ico 1 n,
          (mwVarCDR C n i
            + 2 * (ultimate C n i * laterUltimates C n i) * (mwXi C n i - mwPhi C n i)) := by
  simp only [mwMsepTotalCDR, mwMsepTotalObsCDR, mwCross, mwCrossObs]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mwMsepCDR_eq_mwMsepObsCDR_add_mwVarCDR]
  ring

end Aggregate

end VerifiedReserving
