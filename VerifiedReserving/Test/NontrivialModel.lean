import VerifiedReserving.Ultimate
import VerifiedReserving.SigmaUnbiased
import VerifiedReserving.TotalMsep

/-!
# A nondegenerate Mack model

`Test/Witness.lean` exhibits a degenerate model (no randomness). This file
constructs a genuinely stochastic one and proves it satisfies (M1), (M3) and
(M2') with `σ_0² > 0`, then instantiates the headline theorems on it.

The model: three accident years, three development years, eight equally
likely outcomes. Each accident year `i < 3` carries its own Rademacher shock
`ξ_i` (the `i`-th bit of the outcome), the three shocks being independent and
orthogonal. Claims are

* `C_{i,0} = c` (observed, deterministic), and
* `C_{i,k} = c f^k (1 + s ξ_i)` for `k ≥ 1`,

so the first development step is random with `E[C_{i,1} | D_0] = f c` and
`Var(C_{i,1} | D_0) = c² f² s² = σ_0² c` with `σ_0² = c f² s² > 0`, while later
steps are deterministic multiples (`σ_k² = 0` for `k ≥ 1`). The filtration is
`D_0 = ⊥` (nothing random has been observed yet) and `D_k` = everything for
`k ≥ 1`.

This is the theorem a referee asks for: the hypotheses of the stochastic
layer are jointly satisfiable by a model with positive variance, so the
theorems are not vacuous.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving.NontrivialModel

noncomputable section

abbrev Ω := Fin 8

/-- The uniform probability measure on eight outcomes. -/
def μ : Measure Ω := (8 : ENNReal)⁻¹ • Measure.count

theorem μ_singleton (x : Ω) : μ {x} = (8 : ENNReal)⁻¹ := by
  simp [μ]

instance : IsProbabilityMeasure μ := by
  constructor
  simp [μ, Measure.count_univ]
  norm_num [ENNReal.inv_mul_cancel]

/-- Rademacher shocks: bit `i` of the outcome, as `±1`. -/
def xi (i : ℕ) (ω : Ω) : ℝ :=
  match i with
  | 0 => ![1, -1, 1, -1, 1, -1, 1, -1] ω
  | 1 => ![1, 1, -1, -1, 1, 1, -1, -1] ω
  | 2 => ![1, 1, 1, 1, -1, -1, -1, -1] ω
  | _ => 0

def c : ℝ := 100
def fdev : ℝ := 2
def s : ℝ := 1 / 10

/-- Cumulative claims. -/
def Cw (i k : ℕ) (ω : Ω) : ℝ :=
  if k = 0 then c else c * fdev ^ k * (1 + s * xi i ω)

theorem Cw_zero (i : ℕ) : Cw i 0 = fun _ => c := by
  ext ω; simp [Cw]

theorem Cw_succ (i k : ℕ) : Cw i (k + 1) = fun ω => c * fdev ^ (k + 1) * (1 + s * xi i ω) := by
  ext ω; simp [Cw]

/-- The ambient σ-algebra on `Fin 8` (every set is measurable). -/
abbrev mΩ : MeasurableSpace Ω := inferInstance

@[reducible] def Dfil (k : ℕ) : MeasurableSpace Ω := if k = 0 then ⊥ else mΩ

theorem Dfil_zero : Dfil 0 = ⊥ := by simp [Dfil]
theorem Dfil_succ (k : ℕ) : Dfil (k + 1) = mΩ := by simp [Dfil]

theorem stronglyMeasurable_any (g : Ω → ℝ) : StronglyMeasurable[mΩ] g :=
  (measurable_of_countable _).stronglyMeasurable

/-- The nondegenerate random triangle. -/
def X : RandomTriangle Ω 3 where
  C := Cw
  D := Dfil
  D_le := fun k => by
    cases k with
    | zero => rw [Dfil_zero]; exact bot_le
    | succ k => rw [Dfil_succ]
  D_mono := fun a b hab => by
    cases a with
    | zero =>
      rw [Dfil_zero]; exact bot_le
    | succ a =>
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [Dfil_succ, Dfil_succ]
  meas := fun i j k hjk => by
    cases k with
    | zero =>
      have hj : j = 0 := by omega
      subst hj
      rw [Dfil_zero, Cw_zero]; exact stronglyMeasurable_const
    | succ k =>
      rw [Dfil_succ]; exact stronglyMeasurable_any _

def f : ℕ → ℝ := fun _ => fdev
def σ2 : ℕ → ℝ := fun k => if k = 0 then c * fdev ^ 2 * s ^ 2 else 0

theorem integrable_all (g : Ω → ℝ) : Integrable g μ := Integrable.of_finite

/-- Conditional expectation given `D_0 = ⊥` is the mean, an eight-term sum. -/
theorem condExp_bot_eq_sum (g : Ω → ℝ) :
    μ[g | Dfil 0] = fun _ => (1 / 8 : ℝ) * ∑ ω : Ω, g ω := by
  rw [Dfil_zero, condExp_bot]
  ext _
  rw [integral_fintype (integrable_all g), mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [smul_eq_mul, measureReal_def, μ_singleton]
  norm_num

/-- Conditional expectation given `D_k`, `k ≥ 1`, is the function itself. -/
theorem condExp_succ_eq (k : ℕ) (g : Ω → ℝ) : μ[g | Dfil (k + 1)] =ᵐ[μ] g := by
  rw [Dfil_succ]
  exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable le_rfl (stronglyMeasurable_any g)
    (integrable_all g))

theorem sum_xi (i : ℕ) (hi : i < 3) : ∑ ω : Ω, xi i ω = 0 := by
  interval_cases i <;> simp [xi, Fin.sum_univ_eight]

theorem sum_xi_sq (i : ℕ) (hi : i < 3) : ∑ ω : Ω, xi i ω ^ 2 = 8 := by
  interval_cases i <;> simp [xi, Fin.sum_univ_eight] <;> norm_num

theorem sum_xi_mul (i j : ℕ) (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    ∑ ω : Ω, xi i ω * xi j ω = 0 := by
  interval_cases i <;> interval_cases j <;> simp [xi, Fin.sum_univ_eight] at *

theorem sum_Cw_one (i : ℕ) (hi : i < 3) : ∑ ω : Ω, Cw i 1 ω = 8 * (c * fdev) := by
  rw [Cw_succ]
  simp only [mul_add, mul_one, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_sum, sum_xi i hi]
  ring

theorem mack1 : Mack1 X μ f := by
  intro i hi k
  cases k with
  | zero =>
    show μ[Cw i 1 | Dfil 0] =ᵐ[μ] fun ω => f 0 * Cw i 0 ω
    rw [condExp_bot_eq_sum, sum_Cw_one i hi, Cw_zero]
    refine Eventually.of_forall fun _ => ?_
    simp only [f]; ring
  | succ k =>
    show μ[Cw i (k + 2) | Dfil (k + 1)] =ᵐ[μ] fun ω => f (k + 1) * Cw i (k + 1) ω
    refine (condExp_succ_eq k _).trans (Eventually.of_forall fun ω => ?_)
    rw [Cw_succ, Cw_succ]
    simp only [f]; ring

theorem eps_zero_eq (i : ℕ) : X.eps f i 0 = fun ω => c * fdev * s * xi i ω := by
  ext ω
  simp only [RandomTriangle.eps, X]
  rw [Cw_succ, Cw_zero]
  simp only [f]; ring

theorem eps_succ_eq (i k : ℕ) : X.eps f i (k + 1) = fun _ => 0 := by
  ext ω
  simp only [RandomTriangle.eps, X]
  rw [Cw_succ, Cw_succ]
  simp only [f]; ring

theorem sum_eps_sq (i : ℕ) (hi : i < 3) :
    ∑ ω : Ω, (c * fdev * s * xi i ω) ^ 2 = 8 * (c * fdev * s) ^ 2 := by
  simp only [mul_pow, ← mul_sum, sum_xi_sq i hi]; ring

theorem mack3 : Mack3 X μ f σ2 := by
  intro i hi k
  cases k with
  | zero =>
    show μ[fun ω => (X.eps f i 0 ω) ^ 2 | Dfil 0] =ᵐ[μ] fun ω => σ2 0 * Cw i 0 ω
    rw [eps_zero_eq, condExp_bot_eq_sum, sum_eps_sq i hi, Cw_zero]
    refine Eventually.of_forall fun _ => ?_
    simp only [σ2, ↓reduceIte]; ring
  | succ k =>
    show μ[fun ω => (X.eps f i (k + 1) ω) ^ 2 | Dfil (k + 1)] =ᵐ[μ] fun ω => σ2 (k + 1) * Cw i (k + 1) ω
    rw [eps_succ_eq]
    refine (condExp_succ_eq k _).trans (Eventually.of_forall fun ω => ?_)
    simp [σ2]

theorem sum_eps_mul (i j : ℕ) (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    ∑ ω : Ω, c * fdev * s * xi i ω * (c * fdev * s * xi j ω) = 0 := by
  have : ∀ ω, c * fdev * s * xi i ω * (c * fdev * s * xi j ω) = (c * fdev * s) ^ 2 * (xi i ω * xi j ω) := by
    intro ω; ring
  simp only [this, ← mul_sum, sum_xi_mul i j hi hj hij, mul_zero]

theorem mack2' : Mack2' X μ f := by
  intro k i hi j hj hij
  have hi3 := lt_of_mem_contributors hi
  have hj3 := lt_of_mem_contributors hj
  cases k with
  | zero =>
    show μ[fun ω => X.eps f i 0 ω * X.eps f j 0 ω | Dfil 0] =ᵐ[μ] fun _ => 0
    rw [eps_zero_eq, eps_zero_eq, condExp_bot_eq_sum, sum_eps_mul i j hi3 hj3 hij]
    refine Eventually.of_forall fun _ => ?_
    ring
  | succ k =>
    show μ[fun ω => X.eps f i (k + 1) ω * X.eps f j (k + 1) ω | Dfil (k + 1)] =ᵐ[μ] fun _ => 0
    rw [eps_succ_eq, eps_succ_eq]
    refine (condExp_succ_eq k _).trans (Eventually.of_forall fun ω => ?_)
    simp

theorem σ2_zero_pos : 0 < σ2 0 := by
  simp [σ2, c, fdev, s]

theorem nontrivial : X.C 0 1 (0 : Ω) ≠ X.C 0 1 (1 : Ω) := by
  show Cw 0 1 0 ≠ Cw 0 1 1
  rw [Cw_succ]
  simp [xi, c, fdev, s]
  norm_num

/-- **A nondegenerate Mack model exists.** -/
theorem exists_nontrivial_mack_model :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
      (X' : RandomTriangle Ω' 3) (f' σ2' : ℕ → ℝ),
      Mack1 X' μ' f' ∧ Mack3 X' μ' f' σ2' ∧ Mack2' X' μ' f' ∧ 0 < σ2' 0 ∧
        ∃ ω₁ ω₂, X'.C 0 1 ω₁ ≠ X'.C 0 1 ω₂ :=
  ⟨Ω, inferInstance, μ, inferInstance, X, f, σ2, mack1, mack3, mack2', σ2_zero_pos, 0, 1, nontrivial⟩

/-! ## The headline theorems, instantiated on the nondegenerate model -/

theorem xi_bounds (i : ℕ) (ω : Ω) : -1 ≤ xi i ω ∧ xi i ω ≤ 1 := by
  rcases i with _ | _ | _ | i <;> simp only [xi] <;> fin_cases ω <;> simp

theorem Srv_pos (k : ℕ) (hk : k + 2 ≤ 3) : ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0 := by
  refine Eventually.of_forall fun ω => ?_
  have hk1 : k ≤ 1 := by omega
  interval_cases k
  · show S (X.at ω) 3 0 ≠ 0
    simp only [S, RandomTriangle.at, X, contributors]
    rw [show (3 : ℕ) - 0 - 1 = 2 from rfl, sum_range_succ, sum_range_one, Cw_zero, Cw_zero]
    simp [c]
  · show S (X.at ω) 3 1 ≠ 0
    simp only [S, RandomTriangle.at, X, contributors]
    rw [show (3 : ℕ) - 1 - 1 = 1 from rfl, sum_range_one, Cw_succ]
    have := xi_bounds 0 ω
    simp only [c, fdev, s]
    nlinarith [this.1, this.2]

/-- Theorem 2 on the model: `E[f̂_0 | D_0] = 2`, although `f̂_0` is random. -/
theorem fhat0_unbiased : μ[X.fhatRv 0 | X.D 0] =ᵐ[μ] fun _ => (2 : ℝ) :=
  condExp_fhatRv X f 0 mack1 (Srv_pos 0 (by norm_num)) (fun _ _ => integrable_all _) (integrable_all _)

/-- Theorem 1 on the model, youngest accident year. -/
theorem ultimate_unbiased :
    μ[X.ChatRv 2 2 | X.D (3 - 1 - 2)] =ᵐ[μ] μ[X.C 2 (3 - 1) | X.D (3 - 1 - 2)] :=
  condExp_ultimate_eq X f 2 (by norm_num) mack1 Srv_pos (fun _ _ => integrable_all _)
    (fun _ => integrable_all _) (fun _ => integrable_all _)

/-- The estimation variance on the model: `E[(f̂_0 - 2)² | D_0] = σ_0²/S_0`. -/
theorem var_fhat0 :
    μ[fun ω => (X.fhatRv 0 ω - f 0) ^ 2 | X.D 0] =ᵐ[μ] fun ω => σ2 0 / X.Srv 0 ω :=
  condExp_sq_fhatRv_sub X f σ2 0 mack3 mack2' (Srv_pos 0 (by norm_num))
    (fun _ _ => integrable_all _) (integrable_all _)

/-- Unbiasedness of `σ̂_0²` on the model, where `σ_0² = 4 > 0`. -/
theorem sigma2_unbiased : μ[X.sigma2Rv 0 | X.D 0] =ᵐ[μ] fun _ => σ2 0 :=
  condExp_sigma2Rv X f σ2 0 (by norm_num) mack3 mack2'
    (fun i _ => Eventually.of_forall fun ω => by
      show Cw i 0 ω ≠ 0
      rw [Cw_zero]; simp [c])
    (Srv_pos 0 (by norm_num)) (fun _ _ => integrable_all _) (fun _ => integrable_all _)
    (integrable_all _) (integrable_all _)

/-! ## The cross-term condition of the total reserve, on the model -/

/-- The true ultimates of the model, written out. -/
theorem Cw_two (i : ℕ) : Cw i 2 = fun ω => c * fdev ^ 2 * (1 + s * xi i ω) := by
  ext ω; simp [Cw]

/-- The unconditional mean of the true ultimate is `c f²`. -/
theorem condExp_ultimate_bot (i : ℕ) (hi : i < 3) :
    μ[X.C i 2 | Dfil 0] = fun _ => c * fdev ^ 2 := by
  show μ[Cw i 2 | Dfil 0] = _
  rw [condExp_bot_eq_sum]
  funext _
  interval_cases i <;> simp [Cw, xi, c, fdev, s, Fin.sum_univ_eight] <;> norm_num

/-- **The cross-term condition holds on the nondegenerate model.** The shocks of
different accident years are uncorrelated, so the centred true ultimates are
conditionally uncorrelated given the trivial σ-algebra. -/
theorem crossFree_ultimates : CondCrossFree μ (Dfil 0) (range 3) fun i => X.C i 2 := by
  intro i hi j hj hij
  have hi3 : i < 3 := mem_range.mp hi
  have hj3 : j < 3 := mem_range.mp hj
  rw [condExp_ultimate_bot i hi3, condExp_ultimate_bot j hj3, condExp_bot_eq_sum]
  refine EventuallyEq.of_eq ?_
  funext _
  simp only [Pi.zero_apply]
  interval_cases i <;> interval_cases j <;>
    simp_all [X, Cw, xi, c, fdev, s, Fin.sum_univ_eight] <;> norm_num

/-- The ultimate is genuinely random, so the cross-term condition is not
satisfied for want of randomness. -/
theorem ultimate_nontrivial : X.C 0 2 (0 : Ω) ≠ X.C 0 2 (1 : Ω) := by
  show Cw 0 2 0 ≠ Cw 0 2 1
  rw [Cw_two]
  simp [xi, c, fdev, s]
  norm_num

/-- **The hypotheses of the total-reserve decomposition are not vacuous.** -/
theorem exists_crossFree_nondegenerate :
    CondCrossFree μ (Dfil 0) (range 3) (fun i => X.C i 2)
      ∧ ∃ ω₁ ω₂, X.C 0 2 ω₁ ≠ X.C 0 2 ω₂ :=
  ⟨crossFree_ultimates, 0, 1, ultimate_nontrivial⟩

end

end VerifiedReserving.NontrivialModel
