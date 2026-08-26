import VerifiedReserving.BFPredictionError

/-!
# Finite witness for the stochastic BF model

This one-point model instantiates BF1--BF3 and the conditional prediction-error
theorem. Its increments are all one, so the process variance is zero. The
witness checks joint satisfiability of the new hypotheses; it is not evidence
for positive process variance.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace VerifiedReserving.BFPredictionWitness

noncomputable section

abbrev Omega := Unit

def mu : Measure Omega := Measure.dirac ()

instance : IsProbabilityMeasure mu := by
  unfold mu
  infer_instance

private theorem iIndepFun_const_family {I : Type*} {beta : I -> Type*}
    [forall i, MeasurableSpace (beta i)] (c : forall i, beta i) :
    iIndepFun (fun i (_ : Omega) => c i) mu := by
  rw [iIndepFun_iff]
  intro s f hf
  have hcases : forall i, i ∈ s -> f i = ∅ ∨ f i = Set.univ := by
    intro i hi
    have hmeas := hf i hi
    rw [MeasurableSpace.comap_const] at hmeas
    exact MeasurableSpace.measurableSet_bot_iff.mp hmeas
  by_cases hempty : exists i, i ∈ s ∧ f i = ∅
  · obtain ⟨i, hi, hfi⟩ := hempty
    have hinter : (⋂ j ∈ s, f j) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro omega homega
      have := Set.mem_iInter₂.mp homega i hi
      rw [hfi] at this
      exact this
    have hprod : Finset.prod s (fun j => mu (f j)) = 0 := by
      exact Finset.prod_eq_zero hi (by simp [hfi])
    rw [hinter, hprod]
    simp
  · have hall : forall i, i ∈ s -> f i = Set.univ := by
      intro i hi
      rcases hcases i hi with hfi | hfi
      · exact False.elim (hempty ⟨i, hi, hfi⟩)
      · exact hfi
    have hinter : (⋂ j ∈ s, f j) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro omega
      exact Set.mem_iInter₂.mpr fun i hi => by rw [hall i hi]; trivial
    rw [hinter, measure_univ]
    symm
    exact Finset.prod_eq_one fun i hi => by rw [hall i hi, measure_univ]

/-- Constant cumulative claims `C_{i,k}=k+1`, so every increment is one. -/
def X : RandomTriangle Omega 1 where
  C := fun _ k _ => (k + 1 : Nat)
  D := fun _ => ⊤
  D_le := fun _ => le_top
  D_mono := fun _ _ _ => le_rfl
  meas := fun _ _ _ _ => stronglyMeasurable_const

def x : Nat -> Real := fun _ => 1
def y : Nat -> Real := fun _ => 1
def sigma2 : Nat -> Real := fun _ => 0

theorem bfIncrementRv_eq_one (i k : Nat) :
    X.bfIncrementRv i k = fun _ => 1 := by
  funext omega
  cases k with
  | zero => simp [RandomTriangle.bfIncrementRv, RandomTriangle.at, incr, X]
  | succ k =>
      simp [RandomTriangle.bfIncrementRv, RandomTriangle.at, incr, X]

theorem bf1 : BFFullIncrementIndependence X mu := by
  unfold BFFullIncrementIndependence
  have hconst : (fun p : Nat × Nat => X.bfIncrementRv p.1 p.2) =
      fun _ (_ : Omega) => (1 : Real) := by
    funext p omega
    rw [bfIncrementRv_eq_one]
  rw [hconst]
  exact iIndepFun_const_family fun _ => (1 : Real)

theorem bf2 : BFIncrementMean X mu x y 1 := by
  intro i hi k hk
  rw [bfIncrementRv_eq_one]
  simp [x, y]

theorem bf3 : BFIncrementVariance X mu x sigma2 1 := by
  intro i hi k hk
  rw [bfIncrementRv_eq_one]
  rw [variance_eq_integral stronglyMeasurable_const.aemeasurable]
  simp [x, sigma2]

theorem normalized : BFPatternNormalized y 1 := by
  simp [BFPatternNormalized, y]

theorem increment_memLp (i k : Nat) : MemLp (X.bfIncrementRv i k) 2 mu := by
  rw [bfIncrementRv_eq_one]
  exact memLp_const 1

theorem futureReserve_eq_one : X.bfFutureReserveRv 0 0 1 = fun _ => 1 := by
  funext omega
  simp [RandomTriangle.bfFutureReserveRv, bfIncrementRv_eq_one]

/-- The exact BF mean and process-variance theorems instantiated on the
witness. -/
theorem future_moments :
    integral mu (X.bfFutureReserveRv 0 0 1) = 1 ∧
      variance (X.bfFutureReserveRv 0 0 1) mu = 0 := by
  constructor
  · have h := integral_bfFutureReserveRv X x y 0 0 1 (by decide) (by decide)
      normalized bf2 (fun k hk => (increment_memLp 0 k).integrable one_le_two)
    simpa [x, y, bfCumulativePattern] using h
  · have h := variance_bfFutureReserveRv X x sigma2 0 0 1 (by decide) bf1 bf3
      (fun k hk => increment_memLp 0 k)
    simpa [x, sigma2] using h

/-- The conditional MSEP theorem instantiated with the exact constant
prediction. -/
theorem conditional_msep_zero :
    mu[fun omega => ((1 : Real) - X.bfFutureReserveRv 0 0 1 omega) ^ 2 |
      (⊤ : MeasurableSpace Omega)] =ᵐ[mu] fun _ => 0 := by
  have hpred : MemLp (fun _ : Omega => (1 : Real)) 2 mu := memLp_const 1
  have hindep : (fun _ : Omega => (1 : Real)) ⟂ᵢ[mu] X.bfFutureReserveRv 0 0 1 := by
    rw [futureReserve_eq_one]
    exact indepFun_const_left 1 _
  have hunbiased : integral mu (fun _ : Omega => (1 : Real)) =
      integral mu (X.bfFutureReserveRv 0 0 1) := by
    rw [futureReserve_eq_one]
  have hpair : Measurable fun omega : Omega =>
      ((1 : Real), X.bfFutureReserveRv 0 0 1 omega) := by
    rw [futureReserve_eq_one]
    fun_prop
  have hobs : BFObservedPredictionIndependence mu (⊤ : MeasurableSpace Omega)
      (fun _ : Omega => (1 : Real)) (X.bfFutureReserveRv 0 0 1) := by
    rw [futureReserve_eq_one]
    unfold BFObservedPredictionIndependence
    rw [MeasurableSpace.comap_const]
    exact indep_bot_left _
  have h := condExp_sq_bfPredictionError_eq (G := (⊤ : MeasurableSpace Omega)) X x sigma2
    (fun _ : Omega => (1 : Real)) 0 0 1 le_top (by decide) hpred
    (fun k hk => increment_memLp 0 k) bf1 bf3 hindep hunbiased hpair hobs
  have hvarone : variance (fun _ : Omega => (1 : Real)) mu = 0 := by
    rw [variance_eq_integral stronglyMeasurable_const.aemeasurable]
    simp
  simpa [x, sigma2, hvarone] using h

end

end VerifiedReserving.BFPredictionWitness
