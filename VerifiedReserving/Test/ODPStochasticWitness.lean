import Mathlib.MeasureTheory.Integral.Pi
import VerifiedReserving.ODPStochastic

/-!
# A finite nondegenerate ODP witness

Four incremental cells are independent coordinate variables on a finite
four-coin product space. Each cell is `0` or `2` with equal probability, so its
mean and variance are both `1`. The constant unit mean surface has the source's
corner-constrained log-link form with `c = alpha = beta = 0`, and `phi = 1`.

The witness conditions the future cell `(0, 1)` on the nonempty observed set
`{(0, 0)}`. Thus both mutual independence and observed-versus-future
conditioning are exercised by a concrete model.
-/

open MeasureTheory Finset Filter ProbabilityTheory

namespace VerifiedReserving.ODPWitness

noncomputable section

abbrev Cell := ODPCell 2
abbrev Bit := Fin 2

/-- The uniform probability measure on one two-point coordinate. -/
def coin : Measure Bit := (2 : ENNReal)⁻¹ • Measure.count

theorem coin_singleton (b : Bit) : coin {b} = (2 : ENNReal)⁻¹ := by
  simp [coin]

instance coinIsProbabilityMeasure : IsProbabilityMeasure coin := by
  constructor
  simp [coin, Measure.count_univ]
  norm_num [ENNReal.inv_mul_cancel]

/-- Four independent two-point coordinates, one for each cell of a `2` by `2`
square. -/
abbrev Omega := Cell -> Bit

/-- The product probability measure on the four coordinates. -/
def mu : Measure Omega := Measure.pi fun _ : Cell => coin

instance muIsProbabilityMeasure : IsProbabilityMeasure mu := by
  dsimp [mu]
  infer_instance

/-- A coordinate bit represented as a claim amount. -/
def cellValue (b : Bit) : Real := if b = 0 then 0 else 2

/-- Map natural row and column indices into the witness square. Only indices
below `2` are used by `ODPModel`. -/
def cellIndex (i k : Nat) : Cell := (Fin.ofNat 2 i, Fin.ofNat 2 k)

@[simp] private theorem cellIndex_fin (p : Cell) : cellIndex p.1 p.2 = p := by
  apply Prod.ext
  · apply Fin.ext
    simp [cellIndex]
  · apply Fin.ext
    simp [cellIndex]

/-- The incremental claim in a cell is its independent coordinate value. -/
def X (i k : Nat) (omega : Omega) : Real :=
  cellValue (omega (cellIndex i k))

/-- The unit mean surface. -/
def m (_i _k : Nat) : Real := 1

def phi : Real := 1

theorem integral_cellValue : (∫ b, cellValue b ∂coin) = 1 := by
  rw [integral_fintype (Integrable.of_finite : Integrable cellValue coin)]
  simp [cellValue, coin_singleton, measureReal_def, Fin.sum_univ_two]

theorem variance_cellValue : variance cellValue coin = 1 := by
  rw [variance_eq_integral (measurable_of_countable cellValue).aemeasurable,
    integral_cellValue]
  rw [integral_fintype (Integrable.of_finite :
    Integrable (fun b => (cellValue b - 1) ^ 2) coin)]
  simp [cellValue, coin_singleton, measureReal_def, Fin.sum_univ_two]
  norm_num

@[simp] theorem odpCellRv_X (p : Cell) :
    odpCellRv X p = fun omega => cellValue (omega p) := by
  funext omega
  simp [odpCellRv, X]

theorem integral_X (p : Cell) : (∫ omega, odpCellRv X p omega ∂mu) = 1 := by
  rw [odpCellRv_X, mu,
    integral_comp_eval (μ := fun _ : Cell => coin)
      (i := p) (measurable_of_countable cellValue).aestronglyMeasurable,
    integral_cellValue]

theorem variance_X (p : Cell) : variance (odpCellRv X p) mu = 1 := by
  rw [odpCellRv_X, mu,
    (measurePreserving_eval (fun _ : Cell => coin) p).variance_fun_comp
      (measurable_of_countable cellValue).aemeasurable,
    variance_cellValue]

/-- A concrete model with positive dispersion, corner-constrained log-link
means, and four genuinely independent random cells. -/
theorem model : ODPModel X mu m phi 2 := by
  refine
    { phi_pos := by norm_num [phi]
      log_link := ?_
      measurable := fun _ => measurable_of_countable _
      memLp_two := fun _ => MemLp.of_discrete
      mean_eq := ?_
      variance_eq := ?_
      independent := ?_ }
  · refine ⟨0, fun _ => 0, fun _ => 0, rfl, rfl, ?_⟩
    intro p
    simp [m, logLinkFit]
  · intro p
    simpa [m] using integral_X p
  · intro p
    simpa [m, phi] using variance_X p
  · simpa only [odpCellRv_X, mu] using
      (iIndepFun_pi (μ := fun _ : Cell => coin)
        (X := fun _ : Cell => cellValue)
        (fun _ => (measurable_of_countable cellValue).aemeasurable))

abbrev p00 : Cell := (0, 0)
abbrev p01 : Cell := (0, 1)

/-- The nonempty observed set used by the witness. -/
def observed : Finset Cell := {p00}

private theorem p01_not_mem_observed : p01 ∉ observed := by
  simp [observed, p00, p01]

/-- The witness claims are genuinely random. -/
theorem nontrivial :
    X 0 1 (fun _ => 0) ≠ X 0 1 (fun _ => 1) := by
  norm_num [X, cellIndex, cellValue]

/-- The future coordinate is independent of the nonempty observed vector. -/
theorem independentFutureObserved :
    Indep (odpCellSigma X p01) (odpObservedSigma X observed) mu :=
  odpIndep_cell_observed model p01 observed p01_not_mem_observed

/-- The exact conditional-mean theorem instantiated with one observed cell. -/
theorem conditionalMean :
    mu[odpCellRv X p01 | odpObservedSigma X observed] =ᵐ[mu]
      fun _ => (1 : Real) := by
  simpa [m] using condExp_odpCell_given_observed model p01 observed p01_not_mem_observed

/-- The exact conditional second-moment theorem instantiated with one observed
cell. -/
theorem conditionalVariance :
    mu[fun omega => (odpCellRv X p01 omega - 1) ^ 2 |
      odpObservedSigma X observed] =ᵐ[mu] fun _ => (1 : Real) := by
  simpa [m, phi] using
    condExp_sq_odpCell_sub_given_observed model p01 observed p01_not_mem_observed

/-- Two independent random cells with equal means instantiate the exact MSEP
decomposition nontrivially. -/
theorem twoCellMsep :
    meanSquaredPredictionError (odpCellRv X p01) (odpCellRv X p00) mu = 2 := by
  have hp : p01 ≠ p00 := by
    simp [p01, p00]
  have hi : IndepFun (odpCellRv X p01) (odpCellRv X p00) mu :=
    model.independent.indepFun hp
  have hm : (∫ omega, odpCellRv X p01 omega ∂mu) =
      ∫ omega, odpCellRv X p00 omega ∂mu := by
    rw [model.mean_eq p01, model.mean_eq p00]
    simp [m]
  rw [meanSquaredPredictionError_eq_variance_add
    (model.memLp_two p01) (model.memLp_two p00) hm hi,
    model.variance_eq p01, model.variance_eq p00]
  norm_num [m, phi]

/-- A finite ODP model with multiple independent nondegenerate cells exists. -/
theorem exists_nondegenerate_odp_model :
    ∃ (Omega' : Type) (_ : MeasurableSpace Omega') (mu' : Measure Omega')
      (_ : IsProbabilityMeasure mu') (X' : Nat -> Nat -> Omega' -> Real)
      (m' : Nat -> Nat -> Real) (phi' : Real) (omega0 omega1 : Omega'),
      ODPModel X' mu' m' phi' 2 ∧
        X' 0 1 omega0 ≠ X' 0 1 omega1 :=
  ⟨Omega, inferInstance, mu, inferInstance, X, m, phi,
    fun _ => 0, fun _ => 1, model, nontrivial⟩

end

end VerifiedReserving.ODPWitness
