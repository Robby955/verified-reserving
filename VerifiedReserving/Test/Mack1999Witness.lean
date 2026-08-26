import VerifiedReserving.Mack1999Closure
import VerifiedReserving.Test.IndependenceWitness

/-!
# Finite witnesses for Mack's weighted CL2

The eight-outcome independent-row model is reused for the two weighted
regression cases named by Mack (1999): `α = 0` and `α = 2`.  The first
development factor has a Rademacher shock and positive variance; later factors
are deterministic.  The same model also instantiates the active-contributor
variance theorem with two active observations and one degree of freedom.

The source for the two cases is Mack, ASTIN Bulletin 29 (1999) 361-366,
pp. 362-363.  The finite witness itself is a library non-vacuity check, not a
model or example asserted by the paper.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving.Mack1999Witness

noncomputable section

open NontrivialModel

abbrev X := IndependenceWitness.X

/-- Unit predictable weights on the finite witness. -/
def wUnit : ℕ → ℕ → Ω → ℝ := fun _ _ _ => 1

/-- The factor-scale variance parameter for exponent `α`. -/
def σ2Factor (α : ℕ) : ℕ → ℝ := fun k =>
  if k = 0 then c ^ α * (fdev * s) ^ 2 else 0

theorem factorResidual_zero_eq (i : ℕ) :
    X.factorResidual f i 0 = fun ω => fdev * s * xi i ω := by
  ext ω
  simp only [RandomTriangle.factorResidual, F, RandomTriangle.at, X,
    IndependenceWitness.X]
  rw [Cw_succ, Cw_zero]
  simp [f, c]
  ring

theorem factorResidual_succ_eq (i k : ℕ) :
    X.factorResidual f i (k + 1) = fun _ => 0 := by
  ext ω
  simp only [RandomTriangle.factorResidual, F, RandomTriangle.at, X,
    IndependenceWitness.X]
  rw [Cw_succ, Cw_succ]
  have hpos : 0 < 1 + s * xi i ω := by
    have hxi := xi_bounds i ω
    simp only [s]
    nlinarith
  have hc : c ≠ 0 := by norm_num [c]
  have hf : fdev ≠ 0 := by norm_num [fdev]
  have hp : c * fdev ^ (k + 1) * (1 + s * xi i ω) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ hf)) hpos.ne'
  simp only [f]
  field_simp
  ring

theorem Cw_ne_zero (i k : ℕ) (ω : Ω) : Cw i k ω ≠ 0 := by
  cases k with
  | zero => simp [Cw_zero, c]
  | succ k =>
      rw [Cw_succ]
      have hxi := xi_bounds i ω
      have hpos : 0 < 1 + s * xi i ω := by
        simp only [s]
        nlinarith
      exact mul_ne_zero
        (mul_ne_zero (by norm_num [c]) (pow_ne_zero _ (by norm_num [fdev]))) hpos.ne'

theorem sum_factorResidual_zero_sq (i : ℕ) (hi : i < 3) :
    ∑ ω : Ω, (fdev * s * xi i ω) ^ 2 = 8 * (fdev * s) ^ 2 := by
  simp only [mul_pow, ← mul_sum, sum_xi_sq i hi]
  ring

/-- Weighted CL2 conditioned on each row's own history, for every exponent.
In particular this supplies the `α = 0` and `α = 2` cases. -/
theorem mack3WRow (α : ℕ) : Mack3WRow X μ wUnit α f (σ2Factor α) := by
  constructor
  · intro i k
    exact stronglyMeasurable_const
  · intro i hi k
    cases k with
    | zero =>
        show μ[fun ω => (X.factorResidual f i 0 ω) ^ 2 |
            X.rowSigma i 0] =ᵐ[μ]
          fun ω => σ2Factor α 0 / X.weightVolume wUnit α i 0 ω
        rw [factorResidual_zero_eq, IndependenceWitness.rowSigma_zero,
          ← Dfil_zero, condExp_bot_eq_sum, sum_factorResidual_zero_sq i hi]
        refine Eventually.of_forall fun ω => ?_
        simp only [σ2Factor, if_true, RandomTriangle.weightVolume, wUnit,
          X, IndependenceWitness.X, Cw_zero]
        have hcα : c ^ α ≠ 0 := pow_ne_zero _ (by norm_num [c])
        field_simp
    | succ k =>
        show μ[fun ω => (X.factorResidual f i (k + 1) ω) ^ 2 |
            X.rowSigma i (k + 1)] =ᵐ[μ]
          fun ω => σ2Factor α (k + 1) /
            X.weightVolume wUnit α i (k + 1) ω
        rw [factorResidual_succ_eq]
        simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        change μ[(0 : Ω → ℝ) | X.rowSigma i (k + 1)] =ᵐ[μ]
          fun ω => σ2Factor α (k + 1) /
            X.weightVolume wUnit α i (k + 1) ω
        rw [condExp_zero]
        refine Eventually.of_forall fun ω => ?_
        simp [σ2Factor]

/-- Row-conditioned weighted CL2 transported to the full filtration. -/
theorem mack3W (α : ℕ) : Mack3W X μ wUnit α f (σ2Factor α) :=
  mack3W_of_mack3WRow X wUnit α f (σ2Factor α)
    IndependenceWitness.rowsGenerateD IndependenceWitness.rowsIndep (mack3WRow α)
    (fun _ _ => integrable_all _)

/-- Factor-residual cross terms follow from the independent rows rather than
being imposed separately. -/
theorem mack2Factor'_from_rows : Mack2Factor' X μ f :=
  mack2Factor'_of_rows X f IndependenceWitness.rowsGenerateD
    IndependenceWitness.rowsIndep IndependenceWitness.mack1Row
    (fun i k => Eventually.of_forall fun ω => by
      show Cw i k ω ≠ 0
      exact Cw_ne_zero i k ω)
    (fun _ _ => integrable_all _) (fun _ _ => integrable_all _)
    (fun _ _ _ => integrable_all _)

theorem activeContributors_unit_zero :
    activeContributors 3 0 unitWeights = {0, 1} := by
  simp [activeContributors, contributors, unitWeights]
  decide

theorem activeContributors_unit_zero_card :
    (activeContributors 3 0 unitWeights).card = 2 := by
  rw [activeContributors_unit_zero]
  decide

theorem SWOnRv_unit_zero_ne_zero (α : ℕ) :
    ∀ᵐ ω ∂μ,
      X.SWOnRv wUnit α 0 (activeContributors 3 0 unitWeights) ω ≠ 0 := by
  refine Eventually.of_forall fun ω => ?_
  rw [activeContributors_unit_zero]
  simp [RandomTriangle.SWOnRv, SWOn, RandomTriangle.at, X,
    IndependenceWitness.X, wUnit, Cw_zero, c]

theorem weightVolume_unit_zero_ne_zero (α : ℕ)
    (i : ℕ) (_hi : i ∈ activeContributors 3 0 unitWeights) :
    ∀ᵐ ω ∂μ, X.weightVolume wUnit α i 0 ω ≠ 0 := by
  refine Eventually.of_forall fun ω => ?_
  simp [RandomTriangle.weightVolume, wUnit, X, IndependenceWitness.X,
    Cw_zero, c]

/-- Active-set unbiasedness instantiated on the finite model for any exponent.
The two named Mack cases are exposed below. -/
theorem sigma2WActive_unbiased (α : ℕ) :
    μ[X.sigma2WActiveRv unitWeights α 0 | X.D 0] =ᵐ[μ]
      fun _ => σ2Factor α 0 := by
  have hwEq : (fun i k (_ : Ω) => unitWeights i k) = wUnit := by
    funext i k ω
    rfl
  apply condExp_sigma2WActiveRv X unitWeights α f (σ2Factor α) 0
  · rw [activeContributors_unit_zero_card]
  · rw [hwEq]
    apply mack3WOn_of_mack3W X wUnit α f (σ2Factor α) 0
      (activeContributors 3 0 unitWeights)
    · intro i hi
      exact (mem_activeContributors.mp hi).1
    · exact mack3W α
  · exact mack2Factor'_from_rows
  · intro i hi
    rw [hwEq]
    exact weightVolume_unit_zero_ne_zero α i hi
  · rw [hwEq]
    exact SWOnRv_unit_zero_ne_zero α
  · intro i j
    exact integrable_all _
  · intro i j
    exact integrable_all _
  · intro i
    exact integrable_all _
  · exact integrable_all _
  · exact integrable_all _

/-- Finite non-vacuity witness for Mack's simple-average case `α = 0`. -/
theorem exists_weighted_witness_alpha_zero :
    Mack3WRow X μ wUnit 0 f (σ2Factor 0) ∧
      Mack3W X μ wUnit 0 f (σ2Factor 0) ∧ Mack2Factor' X μ f ∧
      (μ[X.sigma2WActiveRv unitWeights 0 0 | X.D 0] =ᵐ[μ]
        fun _ => σ2Factor 0 0) ∧ 0 < σ2Factor 0 0 ∧
      ∃ ω₁ ω₂, X.C 0 1 ω₁ ≠ X.C 0 1 ω₂ := by
  refine ⟨mack3WRow 0, mack3W 0, mack2Factor'_from_rows,
    sigma2WActive_unbiased 0, ?_, 0, 1, IndependenceWitness.nontrivial⟩
  norm_num [σ2Factor, fdev, s]

/-- Finite non-vacuity witness for Mack's regression case `α = 2`. -/
theorem exists_weighted_witness_alpha_two :
    Mack3WRow X μ wUnit 2 f (σ2Factor 2) ∧
      Mack3W X μ wUnit 2 f (σ2Factor 2) ∧ Mack2Factor' X μ f ∧
      (μ[X.sigma2WActiveRv unitWeights 2 0 | X.D 0] =ᵐ[μ]
        fun _ => σ2Factor 2 0) ∧ 0 < σ2Factor 2 0 ∧
      ∃ ω₁ ω₂, X.C 0 1 ω₁ ≠ X.C 0 1 ω₂ := by
  refine ⟨mack3WRow 2, mack3W 2, mack2Factor'_from_rows,
    sigma2WActive_unbiased 2, ?_, 0, 1, IndependenceWitness.nontrivial⟩
  norm_num [σ2Factor, c, fdev, s]

end

end VerifiedReserving.Mack1999Witness
