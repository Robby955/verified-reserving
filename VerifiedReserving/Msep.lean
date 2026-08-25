import VerifiedReserving.ProcessVariance

/-!
# Process variance and the conditional mean squared error of prediction

For accident year `i` with latest observed development year `d = n-1-i`,
write `M_m = E[C_{i,d+m} | D_d]` and `V_m = E[C_{i,d+m}² | D_d] - M_m²` for the
conditional mean and variance of the true claims `m` steps ahead. Under (M1)
and (M3):

* `M_m = C_{i,d} ∏_{l<m} f_{d+l}` (Theorem 1 side, `condExp_C_of_Mack1`);
* `V_{m+1} = f_{d+m}² V_m + σ_{d+m}² M_m`, `V_0 = 0` (this file), so `V_m` is
  the explicitly computable `procVar` below: Mack's process variance.

For any `D_d`-measurable predictor `P` of `C_{i,d+m}`,

`E[(P - C_{i,d+m})² | D_d] = V_m + (P - M_m)²`,

the conditional mean squared error of prediction splits exactly into process
variance and estimation error. Mack's Theorem 3 estimates the first term by
plugging `f̂, σ̂²` into `procVar` and the second by the conditional-resampling
step; both replacements are recorded as definitions (`mackProcess`,
`mackEstimation`) so the exact statement and the approximation are separate.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

/-- Mack's process variance `m` steps ahead of development year `d`, starting
from claims `c`: the solution of `V_{m+1} = f_{d+m}² V_m + σ_{d+m}² M_m`,
`M_m = c ∏_{l<m} f_{d+l}`, `V_0 = 0`. -/
def procVar (c : ℝ) (f σ2 : ℕ → ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (f (d + m)) ^ 2 * procVar c f σ2 d m
      + σ2 (d + m) * (c * ∏ l ∈ Ico d (d + m), f l)

/-- The closed form: `V_m = ∑_{j<m} (∏_{l=j+1}^{m-1} f_{d+l})² σ_{d+j}² M_j`. -/
theorem procVar_eq_sum (c : ℝ) (f σ2 : ℕ → ℝ) (d m : ℕ) :
    procVar c f σ2 d m
      = ∑ j ∈ range m, (∏ l ∈ Ico (d + j + 1) (d + m), f l) ^ 2
          * (σ2 (d + j) * (c * ∏ l ∈ Ico d (d + j), f l)) := by
  induction m with
  | zero => simp [procVar]
  | succ m ih =>
    rw [procVar, ih, sum_range_succ, mul_sum]
    congr 1
    · refine sum_congr rfl (fun j hj => ?_)
      have hj' : d + j + 1 ≤ d + m := by
        have := mem_range.mp hj; omega
      rw [show d + (m + 1) = d + m + 1 from rfl, prod_Ico_succ_top hj', mul_pow]
      ring
    · rw [show d + (m + 1) = d + m + 1 from rfl, Ico_self]
      simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- **Process variance along a row.** Under (M1) and (M3), with integrability of the
claims, their squares, the residual squares and the cross terms,
`E[C_{i,d+m}² | D_d] - (E[C_{i,d+m} | D_d])² = procVar C_{i,d} f σ² d m` for `d = n-1-i`. -/
theorem condVar_C_eq_procVar [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (σ2 : ℕ → ℝ)
    (i m : ℕ) (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hC : ∀ k, Integrable (X.C i k) μ)
    (hCsq : ∀ k, Integrable (fun ω => (X.C i k ω) ^ 2) μ)
    (hε2 : ∀ k, Integrable (fun ω => (X.eps f i k ω) ^ 2) μ)
    (hCε : ∀ k, Integrable (fun ω => X.C i k ω * X.eps f i k ω) μ) :
    (fun ω => (μ[fun ω => (X.C i (n - 1 - i + m) ω) ^ 2 | X.D (n - 1 - i)]) ω
        - ((μ[X.C i (n - 1 - i + m) | X.D (n - 1 - i)]) ω) ^ 2)
      =ᵐ[μ] fun ω => procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) m := by
  set d := n - 1 - i with hd
  induction m with
  | zero =>
    have h1 : μ[fun ω => (X.C i d ω) ^ 2 | X.D d] =ᵐ[μ] fun ω => (X.C i d ω) ^ 2 := by
      refine (condExp_of_stronglyMeasurable (μ := μ) (X.D_le d)
        (((X.meas i d d le_rfl).measurable.pow_const 2).stronglyMeasurable) (hCsq d)).symm ▸ ?_
      exact Eventually.of_forall fun ω => rfl
    have h2 : μ[X.C i d | X.D d] =ᵐ[μ] X.C i d := by
      refine (condExp_of_stronglyMeasurable (μ := μ) (X.D_le d) (X.meas i d d le_rfl) (hC d)).symm ▸ ?_
      exact Eventually.of_forall fun ω => rfl
    filter_upwards [h1, h2] with ω hω1 hω2
    simp only [Nat.add_zero, procVar]
    rw [hω1, hω2]
    ring
  | succ m ih =>
    have hrec := condExp_sq_C_succ_tower X f σ2 i d (d + m) (Nat.le_add_right _ _) hM h3
      (hC _) (hC _) (hε2 _) (hCε _) (hCsq _)
    have hmean := condExp_C_succ X f i d (d + m) (Nat.le_add_right _ _) hM
    have hM := condExp_C_of_Mack1 X f i m hM hC
    rw [show d + (m + 1) = d + m + 1 from rfl]
    filter_upwards [hrec, hmean, ih, hM] with ω h1 h2 h3' h4
    rw [h1, h2, procVar]
    rw [← hd] at h4
    have h5 : (μ[fun ω => (X.C i (d + m) ω) ^ 2 | X.D d]) ω
        = procVar (X.C i d ω) f σ2 d m + ((μ[X.C i (d + m) | X.D d]) ω) ^ 2 := by
      linarith
    rw [h5, h4]
    ring

/-- Mack's estimator of the process variance: `procVar` with `f̂, σ̂²` plugged in. -/
def mackProcess (C : ℕ → ℕ → ℝ) (n i m : ℕ) : ℝ :=
  procVar (C i (n - 1 - i)) (fhat C n) (sigma2 C n) (n - 1 - i) m

/-- Mack's estimator of the estimation error, obtained from `(Ĉ - M)²` by the
conditional-resampling step: replace `(f̂_k - f_k)²` by its conditional
expectation `σ_k²/S_k` (`condExp_sq_fhatRv_sub`), drop the cross terms
(`condExp_fhatRv_mul`), and plug in `f̂, σ̂²`. This is a definition, not a
theorem: it is the approximation in Mack (1993). -/
def mackEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), sigma2 C n k / (fhat C n k) ^ 2 / S C n k

end

/-! ## The conditional MSEP decomposition and Theorem 3

The conditioning σ-algebra `D` (the observed data) is declared before the
ambient measurable-space instance, following mathlib's convention for
sub-σ-algebras, so that it never shadows the instance. -/
noncomputable section MsepDecomposition

variable {Ω : Type*} {D : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- **Conditional MSEP decomposition.** For a `D`-measurable predictor `P` of an
integrable target `Y` (with `P²`, `PY`, `Y²` integrable),
`E[(P - Y)² | D] = (E[Y² | D] - E[Y | D]²) + (P - E[Y | D])²`. -/
theorem condExp_sq_sub_of_stronglyMeasurable [IsFiniteMeasure μ] (hD : D ≤ ‹MeasurableSpace Ω›)
    (P Y : Ω → ℝ) (hP : StronglyMeasurable[D] P)
    (hY : Integrable Y μ) (hY2 : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hP2 : Integrable (fun ω => (P ω) ^ 2) μ) (hPY : Integrable (P * Y) μ) :
    μ[fun ω => (P ω - Y ω) ^ 2 | D]
      =ᵐ[μ] fun ω => ((μ[fun ω => (Y ω) ^ 2 | D]) ω - ((μ[Y | D]) ω) ^ 2)
                      + (P ω - (μ[Y | D]) ω) ^ 2 := by
  have hexp : (fun ω => (P ω - Y ω) ^ 2)
      = ((fun ω => (P ω) ^ 2) - (2 : ℝ) • (P * Y)) + fun ω => (Y ω) ^ 2 := by
    ext ω; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  rw [hexp]
  have hA := condExp_add (hP2.sub (hPY.smul (2 : ℝ))) hY2 D
  have hB := condExp_sub hP2 (hPY.smul (2 : ℝ)) D
  have hP2' : μ[fun ω => (P ω) ^ 2 | D] =ᵐ[μ] fun ω => (P ω) ^ 2 :=
    EventuallyEq.of_eq (condExp_of_stronglyMeasurable hD
      ((hP.measurable.pow_const 2).stronglyMeasurable) hP2)
  have hPY' : μ[(2 : ℝ) • (P * Y) | D] =ᵐ[μ] (2 : ℝ) • (P * μ[Y | D]) := by
    refine (condExp_smul _ _ _).trans ?_
    have := condExp_mul_of_stronglyMeasurable_left hP hPY hY
    filter_upwards [this] with ω hω
    simp [Pi.smul_apply, hω]
  refine hA.trans ?_
  filter_upwards [hB, hP2', hPY'] with ω h1 h2 h3
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, h1, h2, h3]
  ring

/-- **Mack's Theorem 3, exact form.** Let `D` be the σ-algebra of the observed
data. The chain-ladder prediction `Ĉ_{i,d+m}` is `D`-measurable, and, by
independence across accident years, `D` carries no information about row `i`'s
future beyond `D_d` (hypotheses `hfut1`, `hfut2`: the conditional mean and second
moment of `C_{i,d+m}` given `D` agree with those given `D_d`). Then under (M1)
and (M3) the conditional mean squared error of prediction splits exactly:
`E[(Ĉ_{i,d+m} - C_{i,d+m})² | D] = procVar C_{i,d} f σ² d m + (Ĉ_{i,d+m} - M_m)²`
with `M_m = C_{i,d} ∏_{l<m} f_{d+l}`. The first term is the process variance;
the second is the squared estimation error that Mack's Theorem 3 then
approximates (`mackEstimation`). -/
theorem condMsep_eq [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (f : ℕ → ℝ) (σ2 : ℕ → ℝ) (i m : ℕ) (hD : D ≤ ‹MeasurableSpace Ω›)
    (hPmeas : StronglyMeasurable[D] (X.ChatRv i m))
    (hfut1 : μ[X.C i (n - 1 - i + m) | D] =ᵐ[μ] μ[X.C i (n - 1 - i + m) | X.D (n - 1 - i)])
    (hfut2 : μ[fun ω => (X.C i (n - 1 - i + m) ω) ^ 2 | D]
      =ᵐ[μ] μ[fun ω => (X.C i (n - 1 - i + m) ω) ^ 2 | X.D (n - 1 - i)])
    (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hC : ∀ k, Integrable (X.C i k) μ)
    (hCsq : ∀ k, Integrable (fun ω => (X.C i k ω) ^ 2) μ)
    (hε2 : ∀ k, Integrable (fun ω => (X.eps f i k ω) ^ 2) μ)
    (hCε : ∀ k, Integrable (fun ω => X.C i k ω * X.eps f i k ω) μ)
    (hP2 : Integrable (fun ω => (X.ChatRv i m ω) ^ 2) μ)
    (hPY : Integrable (X.ChatRv i m * X.C i (n - 1 - i + m)) μ) :
    μ[fun ω => (X.ChatRv i m ω - X.C i (n - 1 - i + m) ω) ^ 2 | D]
      =ᵐ[μ] fun ω => procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) m
          + (X.ChatRv i m ω - X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1 - i + m), f l) ^ 2 := by
  have hdec := condExp_sq_sub_of_stronglyMeasurable hD (X.ChatRv i m)
    (X.C i (n - 1 - i + m)) hPmeas (hC _) (hCsq _) hP2 hPY
  have hpv := condVar_C_eq_procVar X f σ2 i m hM h3 hC hCsq hε2 hCε
  have hmean := condExp_C_of_Mack1 X f i m hM hC
  refine hdec.trans ?_
  filter_upwards [hpv, hmean, hfut1, hfut2] with ω h1 h2 h3' h4
  rw [h3', h4, h1, h2]


end MsepDecomposition

end VerifiedReserving
