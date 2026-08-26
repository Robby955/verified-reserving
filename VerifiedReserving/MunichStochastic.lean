import VerifiedReserving.Independence
import VerifiedReserving.MunichChainLadder

/-!
# The Munich chain-ladder stochastic and practical layers

Quarg and Mack, *Munich Chain Ladder* (2004), Sections 2.2 and 3.1.2,
couple cumulative paid and incurred triangles in two distinct layers.

The stochastic layer uses the joint history of the paid and incurred processes
for one accident year.  Its assumptions PQ and IQ regress a standardized future
development residual on the standardized reciprocal paid/incurred ratio.  The
generic theorem `condExp_mul_eq_slope_of_residual_regression` proves the source's
correlation calculation: once the regressor is standardized, the conditional
cross-moment of the two residuals is the regression slope.

The practical layer replaces the conditional quantities by the raw estimators
on pp. 290-292.  The ratio-pattern means, volume-weighted dispersions, four
residual arrays, pooled regression slopes, adjusted development factors and
the coupled recursion are definitions.  The exact theorem
`munichProjection_zero` verifies the source boundary: setting both correlation
parameters to zero gives the two separate chain-ladder projections.
-/

open MeasureTheory Finset Filter ProbabilityTheory

namespace VerifiedReserving

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-! ## Joint paid/incurred histories and conditional residuals -/

/-- A paid and an incurred random triangle on the same probability space.
Their development filtrations may differ; Munich conditioning below uses the
join of their row histories. -/
structure MunichTriangle (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) where
  paid : RandomTriangle Ω n
  incurred : RandomTriangle Ω n

/-- The history of both paid and incurred values of accident year `i` through
development year `k`, Quarg and Mack's `B_i(k)`. -/
@[implicit_reducible]
def MunichTriangle.jointRowSigma (X : MunichTriangle Ω n) (i k : ℕ) : MeasurableSpace Ω :=
  X.paid.rowSigma i k ⊔ X.incurred.rowSigma i k

/-- The whole paid/incurred history of accident year `i`. -/
@[implicit_reducible]
def MunichTriangle.jointRowSigmaAll (X : MunichTriangle Ω n) (i : ℕ) : MeasurableSpace Ω :=
  X.paid.rowSigmaAll i ⊔ X.incurred.rowSigmaAll i

/-- Quarg and Mack's PIU assumption: accident years are independent after paid
and incurred histories are grouped together. -/
def MunichRowsIndep (X : MunichTriangle Ω n) (μ : Measure Ω) : Prop :=
  iIndep X.jointRowSigmaAll μ

/-- The paid individual development factor as a random variable. -/
def MunichTriangle.paidDevelopmentRv (X : MunichTriangle Ω n) (i k : ℕ) : Ω → ℝ :=
  fun ω => X.paid.C i (k + 1) ω / X.paid.C i k ω

/-- The incurred individual development factor as a random variable. -/
def MunichTriangle.incurredDevelopmentRv (X : MunichTriangle Ω n) (i k : ℕ) : Ω → ℝ :=
  fun ω => X.incurred.C i (k + 1) ω / X.incurred.C i k ω

/-- The current paid/incurred ratio `Q_{i,k}` as a random variable. -/
def MunichTriangle.paidIncurredRatioRv (X : MunichTriangle Ω n) (i k : ℕ) : Ω → ℝ :=
  fun ω => X.paid.C i k ω / X.incurred.C i k ω

/-- The reciprocal ratio `Q_{i,k}^{-1}` used in the paid regression. -/
def MunichTriangle.incurredPaidRatioRv (X : MunichTriangle Ω n) (i k : ℕ) : Ω → ℝ :=
  fun ω => X.incurred.C i k ω / X.paid.C i k ω

/-- Conditional standard deviation, represented pointwise as the square root
of mathlib's conditional variance. -/
def conditionalStdDev (μ : Measure Ω) (m : MeasurableSpace Ω) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (Var[Y; μ | m] ω)

/-- Quarg and Mack's conditional residual
`(Y - E[Y | m]) / sqrt(Var[Y | m])`. -/
def conditionalResidual (μ : Measure Ω) (m : MeasurableSpace Ω) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => (Y ω - (μ[Y | m]) ω) / Real.sqrt (Var[Y; μ | m] ω)

/-- PQ: after conditioning on the joint paid/incurred history, the paid
development residual is linear in the reciprocal-ratio residual with the
development-year-independent slope `lambdaPaid`. -/
def MunichPaidRegression (X : MunichTriangle Ω n) (μ : Measure Ω) (lambdaPaid : ℝ) : Prop :=
  ∀ i, i < n → ∀ k,
    μ[conditionalResidual μ (X.paid.rowSigma i k) (X.paidDevelopmentRv i k) |
        X.jointRowSigma i k] =ᵐ[μ]
      fun ω => lambdaPaid *
        conditionalResidual μ (X.paid.rowSigma i k) (X.incurredPaidRatioRv i k) ω

/-- IQ: the incurred development residual is linear in the paid/incurred-ratio
residual with slope `lambdaIncurred`. -/
def MunichIncurredRegression
    (X : MunichTriangle Ω n) (μ : Measure Ω) (lambdaIncurred : ℝ) : Prop :=
  ∀ i, i < n → ∀ k,
    μ[conditionalResidual μ (X.incurred.rowSigma i k) (X.incurredDevelopmentRv i k) |
        X.jointRowSigma i k] =ᵐ[μ]
      fun ω => lambdaIncurred *
        conditionalResidual μ (X.incurred.rowSigma i k) (X.paidIncurredRatioRv i k) ω

omit [MeasurableSpace Ω] in
/-- A residual regression `E[Z | B] = lambda A`, with `A` measurable for `B`
and standardized conditionally on the smaller history `m`, has conditional
cross-moment `lambda`.  This is the calculation on pp. 287-288 that identifies
the Munich regression slopes with residual correlation parameters. -/
theorem condExp_mul_eq_slope_of_residual_regression
    {m B m0 : MeasurableSpace Ω} {ν : Measure[m0] Ω} [IsFiniteMeasure ν]
    {A Z : Ω → ℝ} {lambda : ℝ}
    (hmB : m ≤ B) (hB : B ≤ m0)
    (hAm : StronglyMeasurable[B] A)
    (hZint : Integrable Z ν) (hAZint : Integrable (A * Z) ν)
    (hreg : ν[Z | B] =ᵐ[ν] fun ω => lambda * A ω)
    (hstd : ν[A ^ 2 | m] =ᵐ[ν] fun _ => 1) :
    ν[A * Z | m] =ᵐ[ν] fun _ => lambda := by
  have hpull : ν[A * Z | B] =ᵐ[ν] A * ν[Z | B] :=
    condExp_mul_of_stronglyMeasurable_left hAm hAZint hZint
  have hscaled : ν[A * Z | B] =ᵐ[ν] lambda • (A ^ 2) := by
    refine hpull.trans ?_
    filter_upwards [hreg] with ω hω
    simp only [Pi.mul_apply, hω, Pi.smul_apply, smul_eq_mul, Pi.pow_apply]
    ring
  have htower : ν[A * Z | m] =ᵐ[ν] ν[ν[A * Z | B] | m] :=
    (condExp_condExp_of_le (μ := ν) (f := A * Z) hmB hB).symm
  refine htower.trans ((condExp_congr_ae hscaled).trans ?_)
  have hsmul := condExp_smul (μ := ν) lambda (A ^ 2) m
  filter_upwards [hsmul, hstd] with ω h1 h2
  simp only [h1, Pi.smul_apply, smul_eq_mul, h2, mul_one]

/-- Under PQ and the standardization/integrability conditions of a conditional
residual, the paid standardized residual cross-moment is `lambdaPaid`. -/
theorem munichPaid_residualCorrelation_eq [IsFiniteMeasure μ]
    (X : MunichTriangle Ω n) (lambdaPaid : ℝ) (i k : ℕ) (hi : i < n)
    (hPQ : MunichPaidRegression X μ lambdaPaid)
    (hAmeas : StronglyMeasurable[X.jointRowSigma i k]
      (conditionalResidual μ (X.paid.rowSigma i k) (X.incurredPaidRatioRv i k)))
    (hZint : Integrable
      (conditionalResidual μ (X.paid.rowSigma i k) (X.paidDevelopmentRv i k)) μ)
    (hAZint : Integrable
      (conditionalResidual μ (X.paid.rowSigma i k) (X.incurredPaidRatioRv i k) *
        conditionalResidual μ (X.paid.rowSigma i k) (X.paidDevelopmentRv i k)) μ)
    (hstd : μ[conditionalResidual μ (X.paid.rowSigma i k) (X.incurredPaidRatioRv i k) ^ 2 |
        X.paid.rowSigma i k] =ᵐ[μ] fun _ => 1) :
    μ[conditionalResidual μ (X.paid.rowSigma i k) (X.incurredPaidRatioRv i k) *
        conditionalResidual μ (X.paid.rowSigma i k) (X.paidDevelopmentRv i k) |
      X.paid.rowSigma i k] =ᵐ[μ] fun _ => lambdaPaid := by
  exact condExp_mul_eq_slope_of_residual_regression
    (m0 := inferInstance) (ν := μ)
    (m := X.paid.rowSigma i k) (B := X.jointRowSigma i k)
    (A := conditionalResidual μ (X.paid.rowSigma i k) (X.incurredPaidRatioRv i k))
    (Z := conditionalResidual μ (X.paid.rowSigma i k) (X.paidDevelopmentRv i k))
    (lambda := lambdaPaid)
    (le_sup_left : X.paid.rowSigma i k ≤ X.jointRowSigma i k)
    (sup_le (X.paid.rowSigma_le i k) (X.incurred.rowSigma_le i k))
    hAmeas hZint hAZint (hPQ i hi k) hstd

/-- The IQ analogue: under the residual standardization conditions, the
incurred standardized residual cross-moment is `lambdaIncurred`. -/
theorem munichIncurred_residualCorrelation_eq [IsFiniteMeasure μ]
    (X : MunichTriangle Ω n) (lambdaIncurred : ℝ) (i k : ℕ) (hi : i < n)
    (hIQ : MunichIncurredRegression X μ lambdaIncurred)
    (hAmeas : StronglyMeasurable[X.jointRowSigma i k]
      (conditionalResidual μ (X.incurred.rowSigma i k) (X.paidIncurredRatioRv i k)))
    (hZint : Integrable
      (conditionalResidual μ (X.incurred.rowSigma i k) (X.incurredDevelopmentRv i k)) μ)
    (hAZint : Integrable
      (conditionalResidual μ (X.incurred.rowSigma i k) (X.paidIncurredRatioRv i k) *
        conditionalResidual μ (X.incurred.rowSigma i k) (X.incurredDevelopmentRv i k)) μ)
    (hstd : μ[conditionalResidual μ (X.incurred.rowSigma i k) (X.paidIncurredRatioRv i k) ^ 2 |
        X.incurred.rowSigma i k] =ᵐ[μ] fun _ => 1) :
    μ[conditionalResidual μ (X.incurred.rowSigma i k) (X.paidIncurredRatioRv i k) *
        conditionalResidual μ (X.incurred.rowSigma i k) (X.incurredDevelopmentRv i k) |
      X.incurred.rowSigma i k] =ᵐ[μ] fun _ => lambdaIncurred := by
  exact condExp_mul_eq_slope_of_residual_regression
    (m0 := inferInstance) (ν := μ)
    (m := X.incurred.rowSigma i k) (B := X.jointRowSigma i k)
    (A := conditionalResidual μ (X.incurred.rowSigma i k) (X.paidIncurredRatioRv i k))
    (Z := conditionalResidual μ (X.incurred.rowSigma i k) (X.incurredDevelopmentRv i k))
    (lambda := lambdaIncurred)
    (le_sup_right : X.incurred.rowSigma i k ≤ X.jointRowSigma i k)
    (sup_le (X.paid.rowSigma_le i k) (X.incurred.rowSigma_le i k))
    hAmeas hZint hAZint (hIQ i hi k) hstd

/-! ## Practical estimators from Section 3.1.2 -/

/-- Accident years observed at development year `k`. -/
def mclObservedRows (n k : ℕ) : Finset ℕ := range (n - k)

/-- The raw paid/incurred pattern estimator `qhat_k`, a ratio of observed
paid and incurred column totals. -/
def mclRatioMean (P I : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  (∑ i ∈ mclObservedRows n k, P i k) / ∑ i ∈ mclObservedRows n k, I i k

/-- The incurred-volume dispersion estimator `(rho^I_k)^2` for the
paid/incurred ratios. -/
def mclRatioScaleSqIncurred (P I : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  (1 / ((n : ℝ) - k - 1)) *
    ∑ i ∈ mclObservedRows n k,
      I i k * (paidIncurredRatio P I i k - mclRatioMean P I n k) ^ 2

/-- The paid-volume dispersion estimator `(rho^P_k)^2` for the reciprocal
incurred/paid ratios. -/
def mclRatioScaleSqPaid (P I : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  (1 / ((n : ℝ) - k - 1)) *
    ∑ i ∈ mclObservedRows n k,
      P i k * (paidIncurredRatio I P i k - (mclRatioMean P I n k)⁻¹) ^ 2

/-- Estimated paid development residual. -/
def mclPaidResidual (P : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  (F P i k - fhat P n k) * Real.sqrt (P i k) / Real.sqrt (sigma2 P n k)

/-- Estimated incurred development residual. -/
def mclIncurredResidual (I : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  (F I i k - fhat I n k) * Real.sqrt (I i k) / Real.sqrt (sigma2 I n k)

/-- Estimated reciprocal-ratio residual used in the paid regression. -/
def mclPaidRatioResidual (P I : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  (paidIncurredRatio I P i k - (mclRatioMean P I n k)⁻¹) * Real.sqrt (P i k) /
    Real.sqrt (mclRatioScaleSqPaid P I n k)

/-- Estimated paid/incurred-ratio residual used in the incurred regression. -/
def mclIncurredRatioResidual (P I : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  (paidIncurredRatio P I i k - mclRatioMean P I n k) * Real.sqrt (I i k) /
    Real.sqrt (mclRatioScaleSqIncurred P I n k)

/-- Pooled least-squares slope through the origin for the paid residual plot.
The outer range is `k = 0, ..., n-3`; `contributors n k` supplies the rows
with an observed `k -> k+1` transition. -/
def mclLambdaPaid (P I : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ range (n - 2), ∑ i ∈ contributors n k,
      mclPaidRatioResidual P I n i k * mclPaidResidual P n i k) /
    ∑ k ∈ range (n - 2), ∑ i ∈ contributors n k,
      mclPaidRatioResidual P I n i k ^ 2

/-- Pooled least-squares slope through the origin for the incurred residual
plot. -/
def mclLambdaIncurred (P I : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ range (n - 2), ∑ i ∈ contributors n k,
      mclIncurredRatioResidual P I n i k * mclIncurredResidual I n i k) /
    ∑ k ∈ range (n - 2), ∑ i ∈ contributors n k,
      mclIncurredRatioResidual P I n i k ^ 2

/-- The paid development factor corrected by the current projected
incurred/paid ratio. -/
def mclAdjustedPaidFactor (P I : ℕ → ℕ → ℝ) (n k : ℕ) (lambdaPaid p i : ℝ) : ℝ :=
  fhat P n k + lambdaPaid *
    (Real.sqrt (sigma2 P n k) / Real.sqrt (mclRatioScaleSqPaid P I n k)) *
      (i / p - (mclRatioMean P I n k)⁻¹)

/-- The incurred development factor corrected by the current projected
paid/incurred ratio. -/
def mclAdjustedIncurredFactor
    (P I : ℕ → ℕ → ℝ) (n k : ℕ) (lambdaIncurred p i : ℝ) : ℝ :=
  fhat I n k + lambdaIncurred *
    (Real.sqrt (sigma2 I n k) / Real.sqrt (mclRatioScaleSqIncurred P I n k)) *
      (p / i - mclRatioMean P I n k)

@[simp] theorem mclAdjustedPaidFactor_zero
    (P I : ℕ → ℕ → ℝ) (n k : ℕ) (p i : ℝ) :
    mclAdjustedPaidFactor P I n k 0 p i = fhat P n k := by
  simp [mclAdjustedPaidFactor]

@[simp] theorem mclAdjustedIncurredFactor_zero
    (P I : ℕ → ℕ → ℝ) (n k : ℕ) (p i : ℝ) :
    mclAdjustedIncurredFactor P I n k 0 p i = fhat I n k := by
  simp [mclAdjustedIncurredFactor]

/-- The coupled Munich recursion for one accident year.  Step zero is the
latest observed paid/incurred pair.  Every later step applies the two adjusted
factors simultaneously to the preceding pair. -/
def munichProjection (P I : ℕ → ℕ → ℝ) (n : ℕ)
    (lambdaPaid lambdaIncurred : ℝ) (i : ℕ) : ℕ → ℝ × ℝ
  | 0 => (P i (n - 1 - i), I i (n - 1 - i))
  | m + 1 =>
      let prev := munichProjection P I n lambdaPaid lambdaIncurred i m
      let k := n - 1 - i + m
      (prev.1 * mclAdjustedPaidFactor P I n k lambdaPaid prev.1 prev.2,
        prev.2 * mclAdjustedIncurredFactor P I n k lambdaIncurred prev.1 prev.2)

@[simp] theorem munichProjection_zero_step
    (P I : ℕ → ℕ → ℝ) (n : ℕ) (lambdaPaid lambdaIncurred : ℝ) (i : ℕ) :
    munichProjection P I n lambdaPaid lambdaIncurred i 0 =
      (P i (n - 1 - i), I i (n - 1 - i)) := rfl

theorem munichProjection_succ
    (P I : ℕ → ℕ → ℝ) (n : ℕ) (lambdaPaid lambdaIncurred : ℝ) (i m : ℕ) :
    munichProjection P I n lambdaPaid lambdaIncurred i (m + 1) =
      let prev := munichProjection P I n lambdaPaid lambdaIncurred i m
      let k := n - 1 - i + m
      (prev.1 * mclAdjustedPaidFactor P I n k lambdaPaid prev.1 prev.2,
        prev.2 * mclAdjustedIncurredFactor P I n k lambdaIncurred prev.1 prev.2) := rfl

/-- With both residual correlations set to zero, the coupled recursion is
exactly the pair of separate chain-ladder projections. -/
theorem munichProjection_zero (P I : ℕ → ℕ → ℝ) (n i m : ℕ) :
    munichProjection P I n 0 0 i m =
      (Chat P n i (n - 1 - i + m), Chat I n i (n - 1 - i + m)) := by
  induction m with
  | zero => simp [munichProjection, Chat_diag]
  | succ m ih =>
      rw [munichProjection_succ, ih]
      simp only [mclAdjustedPaidFactor_zero, mclAdjustedIncurredFactor_zero]
      rw [← Chat_succ P n i (n - 1 - i + m) (Nat.le_add_right _ _),
        ← Chat_succ I n i (n - 1 - i + m) (Nat.le_add_right _ _)]
      congr 1

end

end VerifiedReserving
