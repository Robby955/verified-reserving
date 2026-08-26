import VerifiedReserving.ODPStochastic

/-!
# A finite nondegenerate ODP witness

One incremental cell is `0` or `2` with equal probability. Its mean and
variance are both `1`, so it realizes the over-dispersed Poisson moment model
with `phi = 1`. This makes the stochastic moment assumptions non-vacuous;
independence imposes no extra restriction on a single-cell family. No
distributional assumption is added beyond the two moments used by the source.
-/

open MeasureTheory Finset Filter ProbabilityTheory

namespace VerifiedReserving.ODPWitness

noncomputable section

abbrev Omega := Fin 2

/-- Uniform probability on two outcomes. -/
def mu : Measure Omega := (2 : ENNReal)⁻¹ • Measure.count

theorem mu_singleton (omega : Omega) : mu {omega} = (2 : ENNReal)⁻¹ := by
  simp [mu]

instance : IsProbabilityMeasure mu := by
  constructor
  simp [mu, Measure.count_univ]
  norm_num [ENNReal.inv_mul_cancel]

/-- The nonconstant incremental claim. -/
def X (_i _k : Nat) (omega : Omega) : Real :=
  if omega = 0 then 0 else 2

/-- The unit mean surface. -/
def m (_i _k : Nat) : Real := 1

def phi : Real := 1

theorem integral_X (i k : Nat) : (∫ omega, X i k omega ∂mu) = 1 := by
  rw [integral_fintype (Integrable.of_finite : Integrable (X i k) mu)]
  simp [X, mu_singleton, measureReal_def, Fin.sum_univ_two]

theorem variance_X (i k : Nat) : variance (X i k) mu = 1 := by
  rw [variance_eq_integral (measurable_of_countable (X i k)).aemeasurable, integral_X]
  rw [integral_fintype (Integrable.of_finite :
    Integrable (fun omega => (X i k omega - 1) ^ 2) mu)]
  simp [X, mu_singleton, measureReal_def, Fin.sum_univ_two]
  norm_num

/-- A concrete nondegenerate stochastic ODP model. -/
theorem model : ODPModel X mu m phi 1 := by
  refine
    { measurable := fun _ => measurable_of_countable _
      memLp_two := fun _ => MemLp.of_discrete
      mean_eq := ?_
      variance_eq := ?_
      independent := iIndepFun.of_subsingleton }
  · intro p
    simpa [odpCellRv, m] using integral_X p.1 p.2
  · intro p
    simpa [odpCellRv, m, phi] using variance_X p.1 p.2

abbrev p00 : ODPCell 1 := (0, 0)

/-- The witness claim is genuinely random. -/
theorem nontrivial : X 0 0 0 ≠ X 0 0 1 := by
  norm_num [X]

/-- The exact conditional-mean theorem instantiated on the witness, with no
observed cells. -/
theorem conditionalMean :
    mu[odpCellRv X p00 | odpObservedSigma X (∅ : Finset (ODPCell 1))] =ᵐ[mu]
      fun _ => (1 : Real) := by
  simpa [m] using condExp_odpCell_given_observed model p00
    (∅ : Finset (ODPCell 1)) (by simp)

/-- The exact conditional second-moment theorem instantiated on the witness. -/
theorem conditionalVariance :
    mu[fun omega => (odpCellRv X p00 omega - 1) ^ 2 |
      odpObservedSigma X (∅ : Finset (ODPCell 1))] =ᵐ[mu] fun _ => (1 : Real) := by
  simpa [m, phi] using condExp_sq_odpCell_sub_given_observed model p00
    (∅ : Finset (ODPCell 1)) (by simp)

/-- A nondegenerate finite ODP model exists. -/
theorem exists_nondegenerate_odp_model :
    ∃ (Omega' : Type) (_ : MeasurableSpace Omega') (mu' : Measure Omega')
      (_ : IsProbabilityMeasure mu') (X' : Nat -> Nat -> Omega' -> Real)
      (m' : Nat -> Nat -> Real) (phi' : Real) (omega0 omega1 : Omega'),
      ODPModel X' mu' m' phi' 1 ∧
        X' 0 0 omega0 ≠ X' 0 0 omega1 :=
  ⟨Omega, inferInstance, mu, inferInstance, X, m, phi, 0, 1, model, nontrivial⟩

end

end VerifiedReserving.ODPWitness
