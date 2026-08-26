import VerifiedReserving.Independence
import VerifiedReserving.Mack1999

/-!
# Mack (1999): row assumptions and active contributors

Source: T. Mack, *The standard error of chain ladder reserve estimates:
recursive calculation and inclusion of a tail factor*, ASTIN Bulletin 29
(1999) 361-366, especially the weighted CL2 and variance estimator on
pp. 362-363.

This module closes three stochastic gaps left by `Mack1999.lean`.

* `Mack3WRow` states weighted CL2 using an accident year's own history, as in
  Mack's source model.  `mack3W_of_mack3WRow` transports it to the full
  observed-data filtration under independent rows.
* `mack2Factor'_of_rows` derives the factor-residual cross-term condition from
  row independence and row-conditioned CL1.  It is not an extra model
  assumption.
* `sigma2WOn` estimates the factor variance on a fixed active contributor set
  and uses `active.card - 1` degrees of freedom.  A fixed set is important:
  allowing the set itself to depend on the outcome would introduce a random
  selection rule that is absent from Mack's calculation.

The deterministic `activeContributors` filters zero weights.  When cumulative
claims are nonzero, this is exactly the set of nonzero weighted volumes.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-! ## Row-conditioned weighted CL2 -/

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- Mack (1999), pp. 362-363: weighted CL2 conditioned on the history of the accident year.
The first conjunct records that the weights are predictable from that same
history. -/
def Mack3WRow (X : RandomTriangle Ω n) (μ : Measure Ω)
    (w : ℕ → ℕ → Ω → ℝ) (α : ℕ) (f σ2 : ℕ → ℝ) : Prop :=
  (∀ i k, StronglyMeasurable[X.rowSigma i k] (w i k)) ∧
    ∀ i, i < n → ∀ k,
      μ[fun ω => (X.factorResidual f i k ω) ^ 2 | X.rowSigma i k]
        =ᵐ[μ] fun ω => σ2 k / X.weightVolume w α i k ω

/-- A factor residual is measurable with respect to its accident year's full
row sigma-algebra. -/
theorem RandomTriangle.stronglyMeasurable_factorResidual_rowSigmaAll
    (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i k : ℕ) :
    StronglyMeasurable[X.rowSigmaAll i] (X.factorResidual f i k) := by
  unfold RandomTriangle.factorResidual F RandomTriangle.at
  exact ((X.stronglyMeasurable_rowSigmaAll i (k + 1)).div
    (X.stronglyMeasurable_rowSigmaAll i k)).sub stronglyMeasurable_const

/-- **Weighted CL2 on the full observed-data filtration.** Row-conditioned
weighted CL2 and predictable weights transport to `Mack3W` when the rows are
independent and generate `D_k`. -/
theorem mack3W_of_mack3WRow [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α : ℕ)
    (f σ2 : ℕ → ℝ) (hgen : RowsGenerateD X) (hindep : RowsIndep X μ)
    (hrow : Mack3WRow X μ w α f σ2)
    (hint : ∀ i k, Integrable (fun ω => (X.factorResidual f i k ω) ^ 2) μ) :
    Mack3W X μ w α f σ2 := by
  intro i hi k
  rw [X.D_eq_sup hgen i k]
  refine EventuallyEq.trans ?_ (hrow.2 i hi k)
  exact condExp_sup_of_indep (X.rowSigma_le_rowSigmaAll i k) (X.rowSigmaAll_le i)
    (X.otherRowsSigma_le i k) (indep_rowSigmaAll_otherRowsSigma X hindep i k)
    ((X.stronglyMeasurable_factorResidual_rowSigmaAll f i k).pow 2) (hint i k)

/-! ## Factor residual cross terms from row independence -/

/-- Under row-conditioned CL1, an individual factor residual has conditional
mean zero given its row history.  The nonzero claim hypothesis is the source
domain condition needed to identify `F - f` with `eps / C`. -/
theorem condExp_factorResidual_rowSigma [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (f : ℕ → ℝ) (hrow : Mack1Row X μ f)
    {i : ℕ} (hi : i < n) (k : ℕ)
    (hC : ∀ᵐ ω ∂μ, X.C i k ω ≠ 0)
    (hCint : ∀ j, Integrable (X.C i j) μ)
    (hint : Integrable (X.factorResidual f i k) μ) :
    μ[X.factorResidual f i k | X.rowSigma i k] =ᵐ[μ] fun _ => (0 : ℝ) := by
  have hepsint : Integrable (X.eps f i k) μ :=
    (hCint (k + 1)).sub ((hCint k).const_mul (f k))
  have hinv : StronglyMeasurable[X.rowSigma i k] (fun ω => (X.C i k ω)⁻¹) :=
    ((X.stronglyMeasurable_rowSigma i le_rfl).measurable.inv).stronglyMeasurable
  have heq : X.factorResidual f i k =ᵐ[μ]
      (fun ω => (X.C i k ω)⁻¹) * X.eps f i k := by
    filter_upwards [hC] with ω hCω
    simp only [RandomTriangle.factorResidual, RandomTriangle.eps, F,
      RandomTriangle.at, Pi.mul_apply]
    field_simp
  have hpint : Integrable ((fun ω => (X.C i k ω)⁻¹) * X.eps f i k) μ :=
    hint.congr heq
  refine (condExp_congr_ae heq).trans ?_
  refine (condExp_mul_of_stronglyMeasurable_left hinv hpint hepsint).trans ?_
  filter_upwards [condExp_eps_rowSigma X f hrow hi k hCint] with ω hω
  simp [Pi.mul_apply, hω]

/-- **Mack's factor-residual cross condition from independent rows.** This is
the factor analogue of `mack2'_of_rows`, using the same independent-enlargement
and tower argument. -/
theorem mack2Factor'_of_rows [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (f : ℕ → ℝ)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ) (hrow : Mack1Row X μ f)
    (hC : ∀ i k, ∀ᵐ ω ∂μ, X.C i k ω ≠ 0)
    (hCint : ∀ i j, Integrable (X.C i j) μ)
    (hint : ∀ i k, Integrable (X.factorResidual f i k) μ)
    (hprod : ∀ i j k, Integrable (fun ω =>
      X.factorResidual f i k ω * X.factorResidual f j k ω) μ) :
    Mack2Factor' X μ f := by
  intro k i hi j hj hij
  have hi' : i < n := lt_of_mem_contributors hi
  have hm₂le : X.otherRowsSigma i k ⊔ X.rowSigmaAll j ≤ ‹MeasurableSpace Ω› :=
    sup_le (X.otherRowsSigma_le i k) (X.rowSigmaAll_le j)
  have hDle : X.D k ≤ X.rowSigma i k ⊔
      (X.otherRowsSigma i k ⊔ X.rowSigmaAll j) := by
    rw [X.D_eq_sup hgen i k, ← sup_assoc]
    exact le_sup_left
  have hindep' : Indep (X.rowSigmaAll i)
      (X.otherRowsSigma i k ⊔ X.rowSigmaAll j) μ :=
    indep_of_indep_of_le_right (indep_rowSigmaAll_otherRowsAll X hindep i)
      (sup_le (X.otherRowsSigma_le_otherRowsAll i k)
        (X.rowSigmaAll_le_otherRowsAll (Ne.symm hij)))
  have hstepA : μ[X.factorResidual f j k * X.factorResidual f i k |
        X.rowSigma i k ⊔ (X.otherRowsSigma i k ⊔ X.rowSigmaAll j)]
      =ᵐ[μ] X.factorResidual f j k *
        μ[X.factorResidual f i k |
          X.rowSigma i k ⊔ (X.otherRowsSigma i k ⊔ X.rowSigmaAll j)] :=
    condExp_mul_of_stronglyMeasurable_left
      ((X.stronglyMeasurable_factorResidual_rowSigmaAll f j k).mono
        ((le_sup_right : X.rowSigmaAll j ≤ X.otherRowsSigma i k ⊔ X.rowSigmaAll j).trans
          le_sup_right))
      (hprod j i k) (hint i k)
  have hstepB : μ[X.factorResidual f i k |
        X.rowSigma i k ⊔ (X.otherRowsSigma i k ⊔ X.rowSigmaAll j)]
      =ᵐ[μ] μ[X.factorResidual f i k | X.rowSigma i k] :=
    condExp_sup_of_indep (X.rowSigma_le_rowSigmaAll i k) (X.rowSigmaAll_le i) hm₂le hindep'
      (X.stronglyMeasurable_factorResidual_rowSigmaAll f i k) (hint i k)
  have hstepC := condExp_factorResidual_rowSigma X f hrow hi' k (hC i k)
    (fun l => hCint i l) (hint i k)
  have hzero : μ[X.factorResidual f j k * X.factorResidual f i k |
      X.rowSigma i k ⊔ (X.otherRowsSigma i k ⊔ X.rowSigmaAll j)] =ᵐ[μ]
      (0 : Ω → ℝ) := by
    filter_upwards [hstepA, hstepB, hstepC] with ω h1 h2 h3
    rw [h1, Pi.mul_apply, h2, h3]
    simp
  have hcomm : (fun ω => X.factorResidual f i k ω * X.factorResidual f j k ω) =
      X.factorResidual f j k * X.factorResidual f i k := by
    ext ω
    exact mul_comm _ _
  rw [hcomm]
  refine (condExp_condExp_of_le hDle
    (sup_le (X.rowSigma_le i k) hm₂le)).symm.trans ?_
  refine (condExp_congr_ae hzero).trans ?_
  rw [condExp_zero]
  exact Eventually.of_forall fun _ => rfl

/-! ## Active contributors -/

/-- Contributors whose deterministic Mack weight is nonzero. -/
def activeContributors (n k : ℕ) (w : ℕ → ℕ → ℝ) : Finset ℕ :=
  (contributors n k).filter fun i => w i k ≠ 0

theorem mem_activeContributors {n k i : ℕ} {w : ℕ → ℕ → ℝ} :
    i ∈ activeContributors n k w ↔ i ∈ contributors n k ∧ w i k ≠ 0 := by
  simp [activeContributors]

/-- With nonzero cumulative claims, filtering zero weights is equivalent to
filtering zero weighted volumes. -/
theorem mem_activeContributors_iff_volume_ne_zero
    (C : ℕ → ℕ → ℝ) (n k i α : ℕ) (w : ℕ → ℕ → ℝ)
    (hC : C i k ≠ 0) :
    i ∈ activeContributors n k w ↔
      i ∈ contributors n k ∧ w i k * C i k ^ α ≠ 0 := by
  simp [activeContributors, hC]

/-- Weighted column sum over a fixed contributor set. -/
def SWOn (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) (α k : ℕ) (a : Finset ℕ) : ℝ :=
  ∑ i ∈ a, w i k * C i k ^ α

/-- Weighted numerator over a fixed contributor set. -/
def TWOn (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) (α k : ℕ) (a : Finset ℕ) : ℝ :=
  ∑ i ∈ a, w i k * C i k ^ α * F C i k

/-- Generalized development-factor estimate on a fixed active set. -/
def fhatWOn (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) (α k : ℕ) (a : Finset ℕ) : ℝ :=
  TWOn C w α k a / SWOn C w α k a

/-- Active-set form of Mack's weighted variance estimator (1999, p. 363).
The source's sum omits zero-weight observations; the degrees of freedom here
are the number of fixed active observations minus the fitted mean. -/
def sigma2WOn (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) (α k : ℕ) (a : Finset ℕ) : ℝ :=
  (1 / ((a.card : ℝ) - 1)) *
    ∑ i ∈ a, w i k * C i k ^ α * (F C i k - fhatWOn C w α k a) ^ 2

/-- The source-facing active-set estimator, excluding zero deterministic
weights before assigning degrees of freedom. -/
def sigma2WActive (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) : ℝ :=
  sigma2WOn C w α k (activeContributors n k w)

/-- Weighted residual sum of squares on a fixed set. -/
def wssWOn (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) (α k : ℕ)
    (a : Finset ℕ) : ℝ :=
  ∑ i ∈ a, w i k * C i k ^ α * (F C i k - fhatWOn C w α k a) ^ 2

theorem sigma2WOn_eq (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (α k : ℕ) (a : Finset ℕ) :
    sigma2WOn C w α k a = (1 / ((a.card : ℝ) - 1)) * wssWOn C w α k a := rfl

/-- Pointwise residual decomposition on a fixed active set. -/
theorem fhatWOn_sub_eq (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (α k : ℕ) (a : Finset ℕ) (f : ℝ) (hS : SWOn C w α k a ≠ 0) :
    fhatWOn C w α k a - f =
      (SWOn C w α k a)⁻¹ *
        ∑ i ∈ a, (w i k * C i k ^ α) * (F C i k - f) := by
  have hsum :
      (∑ i ∈ a, (w i k * C i k ^ α) * (F C i k - f)) =
        TWOn C w α k a - f * SWOn C w α k a := by
    unfold TWOn SWOn
    calc
      _ = ∑ i ∈ a,
          (w i k * C i k ^ α * F C i k - w i k * C i k ^ α * f) := by
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i ∈ a, w i k * C i k ^ α * F C i k) -
          ∑ i ∈ a, w i k * C i k ^ α * f := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [← Finset.sum_mul]
        ring
  rw [hsum]
  unfold fhatWOn
  field_simp

/-- Squared weighted-mean residual as a double sum on a fixed set. -/
theorem sq_fhatWOn_sub (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (α k : ℕ) (a : Finset ℕ) (f : ℝ) (hS : SWOn C w α k a ≠ 0) :
    (fhatWOn C w α k a - f) ^ 2 =
      (SWOn C w α k a)⁻¹ ^ 2 *
        ∑ i ∈ a, ∑ j ∈ a,
          ((w i k * C i k ^ α) * (F C i k - f)) *
            ((w j k * C j k ^ α) * (F C j k - f)) := by
  rw [fhatWOn_sub_eq C w α k a f hS, mul_pow,
    sq (∑ i ∈ a, (w i k * C i k ^ α) * (F C i k - f)), sum_mul_sum]

/-- Fixed-set weighted sum-of-squares decomposition. -/
theorem weighted_sq_devWOn (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (α k : ℕ) (a : Finset ℕ) (g : ℝ) :
    ∑ i ∈ a, w i k * C i k ^ α * (F C i k - g) ^ 2 =
      (∑ i ∈ a, w i k * C i k ^ α * F C i k ^ 2) -
        2 * g * TWOn C w α k a + g ^ 2 * SWOn C w α k a := by
  unfold TWOn SWOn
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- Fixed-set weighted sum-of-squares decomposition around the true factor. -/
theorem weighted_sq_devWOn_factorResidual
    (C : ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) (α k : ℕ)
    (a : Finset ℕ) (f : ℝ) (hS : SWOn C w α k a ≠ 0) :
    wssWOn C w α k a =
      (∑ i ∈ a, w i k * C i k ^ α * (F C i k - f) ^ 2) -
        SWOn C w α k a * (fhatWOn C w α k a - f) ^ 2 := by
  unfold wssWOn
  have h1 := weighted_sq_devWOn C w α k a (fhatWOn C w α k a)
  have h2 := weighted_sq_devWOn C w α k a f
  have hT : TWOn C w α k a = fhatWOn C w α k a * SWOn C w α k a := by
    unfold fhatWOn
    field_simp
  linear_combination h1 - h2 + (2 * (f - fhatWOn C w α k a)) * hT

/-! ## Conditional unbiasedness on a fixed active set -/

/-- Fixed-set weighted column sum as a random variable. -/
def RandomTriangle.SWOnRv (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) (a : Finset ℕ) : Ω → ℝ :=
  fun ω => SWOn (X.at ω) (fun i k => w i k ω) α k a

/-- Fixed-set generalized development factor as a random variable. -/
def RandomTriangle.fhatWOnRv (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) (a : Finset ℕ) : Ω → ℝ :=
  fun ω => fhatWOn (X.at ω) (fun i k => w i k ω) α k a

/-- Fixed-set weighted residual sum of squares as a random variable. -/
def RandomTriangle.wssWOnRv (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) (a : Finset ℕ) : Ω → ℝ :=
  fun ω => wssWOn (X.at ω) (fun i k => w i k ω) α k a

/-- Fixed-set active variance estimator as a random variable. -/
def RandomTriangle.sigma2WOnRv (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) (a : Finset ℕ) : Ω → ℝ :=
  fun ω => sigma2WOn (X.at ω) (fun i k => w i k ω) α k a

theorem RandomTriangle.SWOnRv_eq_sum (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) (a : Finset ℕ) :
    X.SWOnRv w α k a = ∑ i ∈ a, X.weightVolume w α i k := by
  ext ω
  simp [RandomTriangle.SWOnRv, SWOn, RandomTriangle.weightVolume,
    RandomTriangle.at, Finset.sum_apply]

theorem RandomTriangle.stronglyMeasurable_SWOnRv (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) (a : Finset ℕ)
    (hw : ∀ i ∈ a, StronglyMeasurable[X.D k] (w i k)) :
    StronglyMeasurable[X.D k] (X.SWOnRv w α k a) := by
  rw [X.SWOnRv_eq_sum]
  exact Finset.stronglyMeasurable_sum _ fun i hi =>
    X.stronglyMeasurable_weightVolume w α i k (hw i hi)

/-- Conditional squared error of the fixed-set weighted mean. -/
theorem condExp_sq_fhatWOnRv_sub [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α : ℕ)
    (f σ2 : ℕ → ℝ) (k : ℕ) (a : Finset ℕ)
    (haSub : a ⊆ contributors n k)
    (hw : ∀ i ∈ a, StronglyMeasurable[X.D k] (w i k))
    (h3 : Mack3W X μ w α f σ2) (h2 : Mack2Factor' X μ f)
    (hvol : ∀ i ∈ a, ∀ᵐ ω ∂μ, X.weightVolume w α i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ, X.SWOnRv w α k a ω ≠ 0)
    (hδ : ∀ i j, Integrable (fun ω =>
      X.factorResidual f i k ω * X.factorResidual f j k ω) μ)
    (hweighted : ∀ i j, Integrable (fun ω =>
      (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume w α j k ω * X.factorResidual f j k ω)) μ)
    (hint : Integrable (fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2) μ) :
    μ[fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2 | X.D k]
      =ᵐ[μ] fun ω => σ2 k / X.SWOnRv w α k a ω := by
  set Q : Ω → ℝ := fun ω =>
    ∑ i ∈ a, ∑ j ∈ a,
      (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume w α j k ω * X.factorResidual f j k ω) with hQ
  set W : Ω → ℝ := fun ω => (X.SWOnRv w α k a ω)⁻¹ ^ 2 with hW
  have hrw : (fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2) =ᵐ[μ] W * Q := by
    filter_upwards [hS] with ω hSω
    simp only [Pi.mul_apply, hW, hQ, RandomTriangle.fhatWOnRv,
      RandomTriangle.SWOnRv, RandomTriangle.weightVolume,
      RandomTriangle.factorResidual]
    exact sq_fhatWOn_sub (X.at ω) (fun i k => w i k ω) α k a (f k) hSω
  have hWmeas : StronglyMeasurable[X.D k] W :=
    (((X.stronglyMeasurable_SWOnRv w α k a hw).measurable.inv).pow_const 2).stronglyMeasurable
  have hinnerInt : ∀ i, Integrable (∑ j ∈ a, fun ω =>
      (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume w α j k ω * X.factorResidual f j k ω)) μ :=
    fun i => (integrable_finsetSum a (fun j _ => hweighted i j)).congr
      (Eventually.of_forall fun ω => by simp [Finset.sum_apply])
  have hQint : Integrable Q μ := by
    have h := integrable_finsetSum a (fun i _ => hinnerInt i)
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp [hQ, Finset.sum_apply]
  have hWQint : Integrable (W * Q) μ := hint.congr hrw
  have h1 : μ[fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2 | X.D k]
      =ᵐ[μ] W * μ[Q | X.D k] :=
    (condExp_congr_ae hrw).trans
      (condExp_mul_of_stronglyMeasurable_left hWmeas hWQint hQint)
  have hQ' : Q = ∑ i ∈ a, ∑ j ∈ a, fun ω =>
      (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume w α j k ω * X.factorResidual f j k ω) := by
    ext ω
    simp [hQ, Finset.sum_apply]
  have h2' : μ[Q | X.D k] =ᵐ[μ]
      fun ω => σ2 k * X.SWOnRv w α k a ω := by
    rw [hQ']
    have hsum := condExp_finsetSum (μ := μ) (m := X.D k) (s := a)
      (f := fun i => ∑ j ∈ a, fun ω =>
        (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
          (X.weightVolume w α j k ω * X.factorResidual f j k ω))
      (fun i _ => hinnerInt i)
    refine hsum.trans ?_
    have hinner : ∀ i ∈ a,
        μ[∑ j ∈ a, fun ω =>
          (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
            (X.weightVolume w α j k ω * X.factorResidual f j k ω) | X.D k]
          =ᵐ[μ] fun ω => σ2 k * X.weightVolume w α i k ω := by
      intro i hi
      have hs := condExp_finsetSum (μ := μ) (m := X.D k) (s := a)
        (f := fun j => fun ω =>
          (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
            (X.weightVolume w α j k ω * X.factorResidual f j k ω))
        (fun j _ => hweighted i j)
      refine hs.trans ?_
      have hterm : ∀ j ∈ a,
          μ[fun ω =>
            (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
              (X.weightVolume w α j k ω * X.factorResidual f j k ω) | X.D k]
            =ᵐ[μ] fun ω => if j = i then
              σ2 k * X.weightVolume w α i k ω else 0 := by
        intro j hj
        by_cases hij : j = i
        · subst j
          let v : Ω → ℝ := X.weightVolume w α i k
          let d : Ω → ℝ := X.factorResidual f i k
          have hvmeas : StronglyMeasurable[X.D k] (v * v) :=
            (X.stronglyMeasurable_weightVolume w α i k (hw i hi)).mul
              (X.stronglyMeasurable_weightVolume w α i k (hw i hi))
          have hd2 : Integrable (fun ω => (d ω) ^ 2) μ :=
            (hδ i i).congr (Eventually.of_forall fun ω => by simp [d, sq])
          have heq : (fun ω => (v ω * d ω) * (v ω * d ω)) =
              (v * v) * fun ω => (d ω) ^ 2 := by
            ext ω
            simp [Pi.mul_apply]
            ring
          rw [show (fun ω =>
              (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
                (X.weightVolume w α i k ω * X.factorResidual f i k ω)) =
              (fun ω => (v ω * d ω) * (v ω * d ω)) by rfl, heq]
          refine (condExp_mul_of_stronglyMeasurable_left hvmeas
            (by rw [← heq]; exact hweighted i i) hd2).trans ?_
          filter_upwards [h3 i (lt_of_mem_contributors (haSub hi)) k, hvol i hi]
            with ω h3ω hvω
          simp only [Pi.mul_apply, d, h3ω, v, if_true]
          field_simp
        · have hvmeas : StronglyMeasurable[X.D k]
              (X.weightVolume w α i k * X.weightVolume w α j k) :=
            (X.stronglyMeasurable_weightVolume w α i k (hw i hi)).mul
              (X.stronglyMeasurable_weightVolume w α j k (hw j hj))
          have heq : (fun ω =>
              (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
                (X.weightVolume w α j k ω * X.factorResidual f j k ω)) =
              (X.weightVolume w α i k * X.weightVolume w α j k) *
                fun ω => X.factorResidual f i k ω * X.factorResidual f j k ω := by
            ext ω
            simp [Pi.mul_apply]
            ring
          rw [heq]
          refine (condExp_mul_of_stronglyMeasurable_left hvmeas
            (by rw [← heq]; exact hweighted i j) (hδ i j)).trans ?_
          filter_upwards [h2 k i (haSub hi) j (haSub hj) (Ne.symm hij)] with ω h2ω
          simp [Pi.mul_apply, h2ω, hij]
      have hall : ∀ᵐ ω ∂μ, ∀ j ∈ a,
          (μ[fun ω =>
            (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
              (X.weightVolume w α j k ω * X.factorResidual f j k ω) | X.D k]) ω =
            if j = i then σ2 k * X.weightVolume w α i k ω else 0 := by
        rw [eventually_all_finset]
        exact hterm
      filter_upwards [hall] with ω hω
      rw [Finset.sum_apply, Finset.sum_congr rfl (fun j hj => hω j hj),
        Finset.sum_ite_eq' a i]
      simp [hi]
    have hall' : ∀ᵐ ω ∂μ, ∀ i ∈ a,
        (μ[∑ j ∈ a, fun ω =>
          (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
            (X.weightVolume w α j k ω * X.factorResidual f j k ω) | X.D k]) ω =
          σ2 k * X.weightVolume w α i k ω := by
      rw [eventually_all_finset]
      exact hinner
    filter_upwards [hall'] with ω hω
    rw [Finset.sum_apply, Finset.sum_congr rfl (fun i hi => hω i hi),
      ← Finset.mul_sum, X.SWOnRv_eq_sum, Finset.sum_apply]
  refine h1.trans ?_
  filter_upwards [h2', hS] with ω h2ω hSω
  simp only [Pi.mul_apply, h2ω, hW]
  field_simp

/-- The active weighted residual sum of squares has conditional expectation
`(active.card - 1) * σ²`. -/
theorem condExp_wssWOnRv [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α : ℕ)
    (f σ2 : ℕ → ℝ) (k : ℕ) (a : Finset ℕ)
    (haSub : a ⊆ contributors n k)
    (hw : ∀ i ∈ a, StronglyMeasurable[X.D k] (w i k))
    (h3 : Mack3W X μ w α f σ2) (h2 : Mack2Factor' X μ f)
    (hvol : ∀ i ∈ a, ∀ᵐ ω ∂μ, X.weightVolume w α i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ, X.SWOnRv w α k a ω ≠ 0)
    (hδ : ∀ i j, Integrable (fun ω =>
      X.factorResidual f i k ω * X.factorResidual f j k ω) μ)
    (hweighted : ∀ i j, Integrable (fun ω =>
      (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume w α j k ω * X.factorResidual f j k ω)) μ)
    (hweightedSq : ∀ i, Integrable (fun ω =>
      X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2) μ)
    (hsq : Integrable (fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2) μ)
    (hSsq : Integrable (fun ω =>
      X.SWOnRv w α k a ω * (X.fhatWOnRv w α k a ω - f k) ^ 2) μ) :
    μ[X.wssWOnRv w α k a | X.D k] =ᵐ[μ]
      fun _ => ((a.card : ℝ) - 1) * σ2 k := by
  set A : Ω → ℝ := fun ω => ∑ i ∈ a,
    X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2 with hA
  set B : Ω → ℝ := fun ω =>
    X.SWOnRv w α k a ω * (X.fhatWOnRv w α k a ω - f k) ^ 2 with hB
  have hrw : X.wssWOnRv w α k a =ᵐ[μ] A - B := by
    filter_upwards [hS] with ω hSω
    simp only [Pi.sub_apply, hA, hB, RandomTriangle.wssWOnRv,
      RandomTriangle.factorResidual, RandomTriangle.SWOnRv,
      RandomTriangle.fhatWOnRv, RandomTriangle.weightVolume]
    exact weighted_sq_devWOn_factorResidual (X.at ω) (fun i k => w i k ω)
      α k a (f k) hSω
  have hAint : Integrable A μ :=
    (integrable_finsetSum a (fun i _ => hweightedSq i)).congr
      (Eventually.of_forall fun ω => by simp [hA])
  have hBint : Integrable B μ := hSsq
  have hAcond : μ[A | X.D k] =ᵐ[μ] fun _ => (a.card : ℝ) * σ2 k := by
    have hA' : A = ∑ i ∈ a, fun ω =>
        X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2 := by
      ext ω
      simp [hA, Finset.sum_apply]
    rw [hA']
    have hsum := condExp_finsetSum (μ := μ) (m := X.D k) (s := a)
      (f := fun i => fun ω =>
        X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2)
      (fun i _ => hweightedSq i)
    refine hsum.trans ?_
    have hterm : ∀ i ∈ a,
        μ[fun ω =>
          X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2 | X.D k]
          =ᵐ[μ] fun _ => σ2 k := by
      intro i hi
      have hvmeas := X.stronglyMeasurable_weightVolume w α i k (hw i hi)
      have hd2 : Integrable (fun ω => (X.factorResidual f i k ω) ^ 2) μ :=
        (hδ i i).congr (Eventually.of_forall fun ω => by simp [sq])
      refine (condExp_mul_of_stronglyMeasurable_left hvmeas
        (hweightedSq i) hd2).trans ?_
      filter_upwards [h3 i (lt_of_mem_contributors (haSub hi)) k, hvol i hi]
        with ω h3ω hvω
      simp only [Pi.mul_apply, h3ω]
      field_simp
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ a,
        (μ[fun ω =>
          X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2 | X.D k]) ω =
          σ2 k := by
      rw [eventually_all_finset]
      exact hterm
    filter_upwards [hall] with ω hω
    rw [Finset.sum_apply, Finset.sum_congr rfl (fun i hi => hω i hi),
      Finset.sum_const, nsmul_eq_mul]
  have hBcond : μ[B | X.D k] =ᵐ[μ] fun _ => σ2 k := by
    have heq : B = X.SWOnRv w α k a *
        fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2 := by
      ext ω
      simp [hB]
    rw [heq]
    refine (condExp_mul_of_stronglyMeasurable_left
      (X.stronglyMeasurable_SWOnRv w α k a hw)
      (by rw [← heq]; exact hBint) hsq).trans ?_
    filter_upwards [condExp_sq_fhatWOnRv_sub X w α f σ2 k a haSub hw h3 h2
      hvol hS hδ hweighted hsq, hS] with ω hω hSω
    simp only [Pi.mul_apply, hω]
    field_simp
  have hfinal : μ[X.wssWOnRv w α k a | X.D k] =ᵐ[μ]
      μ[A | X.D k] - μ[B | X.D k] :=
    (condExp_congr_ae hrw).trans (condExp_sub hAint hBint (X.D k))
  refine hfinal.trans ?_
  filter_upwards [hAcond, hBcond] with ω hAω hBω
  simp only [Pi.sub_apply, hAω, hBω]
  ring

/-- **Unbiased active-contributor variance estimator.** This supplies the
conditional-unbiasedness calculation behind Mack's p. 363 estimator. With at least two
active observations, `sigma2WOn` uses `active.card - 1` and is conditionally
unbiased under weighted CL2 and independent-row cross terms. -/
theorem condExp_sigma2WOnRv [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α : ℕ)
    (f σ2 : ℕ → ℝ) (k : ℕ) (a : Finset ℕ) (hcard : 2 ≤ a.card)
    (haSub : a ⊆ contributors n k)
    (hw : ∀ i ∈ a, StronglyMeasurable[X.D k] (w i k))
    (h3 : Mack3W X μ w α f σ2) (h2 : Mack2Factor' X μ f)
    (hvol : ∀ i ∈ a, ∀ᵐ ω ∂μ, X.weightVolume w α i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ, X.SWOnRv w α k a ω ≠ 0)
    (hδ : ∀ i j, Integrable (fun ω =>
      X.factorResidual f i k ω * X.factorResidual f j k ω) μ)
    (hweighted : ∀ i j, Integrable (fun ω =>
      (X.weightVolume w α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume w α j k ω * X.factorResidual f j k ω)) μ)
    (hweightedSq : ∀ i, Integrable (fun ω =>
      X.weightVolume w α i k ω * (X.factorResidual f i k ω) ^ 2) μ)
    (hsq : Integrable (fun ω => (X.fhatWOnRv w α k a ω - f k) ^ 2) μ)
    (hSsq : Integrable (fun ω =>
      X.SWOnRv w α k a ω * (X.fhatWOnRv w α k a ω - f k) ^ 2) μ) :
    μ[X.sigma2WOnRv w α k a | X.D k] =ᵐ[μ] fun _ => σ2 k := by
  have h := condExp_wssWOnRv X w α f σ2 k a haSub hw h3 h2 hvol hS
    hδ hweighted hweightedSq hsq hSsq
  have heq : X.sigma2WOnRv w α k a =
      (1 / ((a.card : ℝ) - 1)) • X.wssWOnRv w α k a := by
    ext ω
    simp [RandomTriangle.sigma2WOnRv, RandomTriangle.wssWOnRv,
      sigma2WOn_eq, smul_eq_mul]
  rw [heq]
  refine (condExp_smul _ _ _).trans ?_
  have hne : (a.card : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show a.card ≠ 1 by omega))
  filter_upwards [h] with ω hω
  simp only [Pi.smul_apply, smul_eq_mul, hω]
  field_simp

/-- Random-variable form of the deterministic zero-weight active estimator. -/
def RandomTriangle.sigma2WActiveRv (X : RandomTriangle Ω n)
    (w : ℕ → ℕ → ℝ) (α k : ℕ) : Ω → ℝ :=
  X.sigma2WOnRv (fun i k _ => w i k) α k (activeContributors n k w)

/-- Conditional unbiasedness of the source-facing active estimator. -/
theorem condExp_sigma2WActiveRv [IsFiniteMeasure μ]
    (X : RandomTriangle Ω n) (w : ℕ → ℕ → ℝ) (α : ℕ)
    (f σ2 : ℕ → ℝ) (k : ℕ)
    (hcard : 2 ≤ (activeContributors n k w).card)
    (h3 : Mack3W X μ (fun i k _ => w i k) α f σ2)
    (h2 : Mack2Factor' X μ f)
    (hvol : ∀ i ∈ activeContributors n k w, ∀ᵐ ω ∂μ,
      X.weightVolume (fun i k _ => w i k) α i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ,
      X.SWOnRv (fun i k _ => w i k) α k (activeContributors n k w) ω ≠ 0)
    (hδ : ∀ i j, Integrable (fun ω =>
      X.factorResidual f i k ω * X.factorResidual f j k ω) μ)
    (hweighted : ∀ i j, Integrable (fun ω =>
      (X.weightVolume (fun i k _ => w i k) α i k ω * X.factorResidual f i k ω) *
        (X.weightVolume (fun i k _ => w i k) α j k ω * X.factorResidual f j k ω)) μ)
    (hweightedSq : ∀ i, Integrable (fun ω =>
      X.weightVolume (fun i k _ => w i k) α i k ω *
        (X.factorResidual f i k ω) ^ 2) μ)
    (hsq : Integrable (fun ω =>
      (X.fhatWOnRv (fun i k _ => w i k) α k (activeContributors n k w) ω - f k) ^ 2) μ)
    (hSsq : Integrable (fun ω =>
      X.SWOnRv (fun i k _ => w i k) α k (activeContributors n k w) ω *
        (X.fhatWOnRv (fun i k _ => w i k) α k (activeContributors n k w) ω - f k) ^ 2) μ) :
    μ[X.sigma2WActiveRv w α k | X.D k] =ᵐ[μ] fun _ => σ2 k := by
  apply condExp_sigma2WOnRv X (fun i k _ => w i k) α f σ2 k
    (activeContributors n k w) hcard
  · intro i hi
    exact (mem_activeContributors.mp hi).1
  · intro i _
    exact stronglyMeasurable_const
  · exact h3
  · exact h2
  · exact hvol
  · exact hS
  · exact hδ
  · exact hweighted
  · exact hweightedSq
  · exact hsq
  · exact hSsq

end

end VerifiedReserving
