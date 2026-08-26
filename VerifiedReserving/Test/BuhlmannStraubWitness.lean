import VerifiedReserving.BuhlmannStraubStochastic

/-!
# A finite stochastic Bühlmann-Straub witness

This two-outcome model has one exposure period, constant latent mean `1`, and
a genuine process shock: the observed loss ratio is `0` or `2` with equal
probability. Its conditional process variance is `1`. It verifies that the
stochastic moment hypotheses are jointly satisfiable with positive process
variance and a nonconstant observation.

The latent between-risk variance is zero in this smallest witness. The general
theorems do not impose that restriction.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving.BuhlmannStraubWitness

noncomputable section

abbrev Ω := Fin 2
abbrev Θ := Unit
abbrev ι := Fin 1

/-- Uniform probability measure on two outcomes. -/
def μ : Measure Ω := (2 : ENNReal)⁻¹ • Measure.count

instance : IsProbabilityMeasure μ := by
  constructor
  simp [μ, Measure.count_univ]
  norm_num [ENNReal.inv_mul_cancel]

def sample : Finset ι := univ
def weight : ι → ℝ := fun _ => 1
def theta : Ω → Θ := fun _ => ()
def hypotheticalMean : Θ → ℝ := fun _ => 1
def hypotheticalVariance : Θ → ℝ := fun _ => 1
def observation : ι → Ω → ℝ := fun _ omega => ![0, 2] omega

theorem processShock_integrable (g : Ω → ℝ) : Integrable g μ :=
  Integrable.of_finite

theorem processShock_memLp (g : Ω → ℝ) : MemLp g 2 μ := by
  refine (memLp_two_iff_integrable_sq
    (measurable_of_countable g).aestronglyMeasurable).2 ?_
  exact processShock_integrable _

theorem integral_eq_average (g : Ω → ℝ) :
    ∫ omega, g omega ∂μ = (1 / 2 : ℝ) * ∑ omega : Ω, g omega := by
  rw [integral_fintype (processShock_integrable g), mul_sum]
  refine sum_congr rfl fun omega _ => ?_
  rw [smul_eq_mul, measureReal_def]
  simp [μ]

theorem latentSigma_eq_bot : buhlmannStraubLatentSigma theta = ⊥ := by
  change MeasurableSpace.comap (fun _ : Ω => ()) inferInstance = ⊥
  exact MeasurableSpace.comap_const ()

theorem condExp_bot_eq_average (g : Ω → ℝ) :
    μ[g | ⊥] = fun _ => (1 / 2 : ℝ) * ∑ omega : Ω, g omega := by
  rw [condExp_bot]
  ext omega
  exact integral_eq_average g

/-- The observed loss ratio is genuinely random. -/
theorem observation_nondegenerate : observation 0 0 ≠ observation 0 1 := by
  norm_num [observation]

/-- The finite process-shock model satisfies every stochastic
Bühlmann-Straub moment assumption with `m=1`, `v=1`, and `w=0`. -/
theorem momentModel :
    BuhlmannStraubMomentModel sample weight theta hypotheticalMean
      hypotheticalVariance observation 1 1 0 μ := by
  constructor
  · rw [latentSigma_eq_bot]
    exact bot_le
  · change StronglyMeasurable[buhlmannStraubLatentSigma theta] (fun _ : Ω => (1 : ℝ))
    exact stronglyMeasurable_const
  · exact processShock_memLp _
  · change StronglyMeasurable[buhlmannStraubLatentSigma theta] (fun _ : Ω => (1 : ℝ))
    exact stronglyMeasurable_const
  · exact processShock_integrable _
  · intro i hi
    exact processShock_memLp _
  · intro i hi
    simp [weight]
  · intro i hi
    rw [latentSigma_eq_bot, condExp_bot_eq_average]
    exact Eventually.of_forall fun omega => by
      fin_cases i
      norm_num [observation, buhlmannStraubRiskMean, hypotheticalMean, theta,
        Fin.sum_univ_two]
  · intro i hi
    rw [latentSigma_eq_bot, condExp_bot_eq_average]
    exact Eventually.of_forall fun omega => by
      fin_cases i
      norm_num [observation, buhlmannStraubResidual, buhlmannStraubRiskMean,
        buhlmannStraubRiskVariance, hypotheticalMean, hypotheticalVariance, theta,
        weight, Fin.sum_univ_two]
  · intro i hi j hj hij
    fin_cases i
    fin_cases j
    exact (hij rfl).elim
  · rw [integral_eq_average]
    norm_num [buhlmannStraubRiskMean, hypotheticalMean, theta, Fin.sum_univ_two]
  · rw [integral_eq_average]
    norm_num [buhlmannStraubRiskVariance, hypotheticalVariance, theta, Fin.sum_univ_two]
  · rw [integral_eq_average]
    norm_num [buhlmannStraubRiskMean, hypotheticalMean, theta, Fin.sum_univ_two]

/-- Non-vacuity in one declaration: there is a finite model with positive
process variance and a nonconstant observation. -/
theorem exists_process_nondegenerate_buhlmannStraubModel :
    0 < (1 : ℝ) ∧ observation 0 0 ≠ observation 0 1 ∧
      BuhlmannStraubMomentModel sample weight theta hypotheticalMean
        hypotheticalVariance observation 1 1 0 μ := by
  exact ⟨by norm_num, observation_nondegenerate, momentModel⟩

end

end VerifiedReserving.BuhlmannStraubWitness
