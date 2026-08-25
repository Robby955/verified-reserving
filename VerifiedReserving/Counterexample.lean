import VerifiedReserving.Catalogue

/-!
# A strict counterexample: the two estimation-error estimators differ

`Catalogue.lean` proves `mackEstimation ≤ bbmwEstimation` and gives the exact
difference `Ĉ² (∏(1 + a_k) - 1 - ∑ a_k)`. This file exhibits a concrete run-off
triangle on which the difference is strictly positive, so the two published
estimators of the estimation error are not the same estimator.

The triangle has four accident years and four development years. Its
individual development factors in the first two columns are not all equal,
so `σ̂_0² > 0` and `σ̂_1² > 0`, hence `a_0 > 0` and `a_1 > 0` along the row of
the youngest accident year, and the remainder `∏(1+a_k) - 1 - ∑ a_k`
contains the product `a_0 a_1 > 0`.

Every number below is checked by `norm_num` from the definitions; nothing
is asserted numerically without proof.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- The counterexample triangle (rows: accident years 0..3; columns: development
years 0..3; unobserved cells are `0` and never read by the estimators). -/
def Cex : ℕ → ℕ → ℝ
  | 0, 0 => 100 | 0, 1 => 200 | 0, 2 => 260 | 0, 3 => 280
  | 1, 0 => 110 | 1, 1 => 200 | 1, 2 => 270
  | 2, 0 => 90  | 2, 1 => 200
  | 3, 0 => 120
  | _, _ => 0

theorem Cex_contributors0 : contributors 4 0 = {0, 1, 2} := by decide
theorem Cex_contributors1 : contributors 4 1 = {0, 1} := by decide
theorem Cex_contributors2 : contributors 4 2 = {0} := by decide

theorem Cex_S0 : S Cex 4 0 = 300 := by
  simp [S, Cex_contributors0, Cex]; norm_num
theorem Cex_T0 : T Cex 4 0 = 600 := by
  simp [T, Cex_contributors0, Cex]; norm_num
theorem Cex_fhat0 : fhat Cex 4 0 = 2 := by
  rw [fhat, Cex_S0, Cex_T0]; norm_num

theorem Cex_S1 : S Cex 4 1 = 400 := by
  simp [S, Cex_contributors1, Cex]; norm_num
theorem Cex_T1 : T Cex 4 1 = 530 := by
  simp [T, Cex_contributors1, Cex]; norm_num
theorem Cex_fhat1 : fhat Cex 4 1 = 53 / 40 := by
  rw [fhat, Cex_S1, Cex_T1]; norm_num

theorem Cex_S2 : S Cex 4 2 = 260 := by
  simp [S, Cex_contributors2, Cex]
theorem Cex_T2 : T Cex 4 2 = 280 := by
  simp [T, Cex_contributors2, Cex]
theorem Cex_fhat2 : fhat Cex 4 2 = 14 / 13 := by
  rw [fhat, Cex_S2, Cex_T2]; norm_num

/-- `σ̂_0² = (1/2) ∑_{i<3} C_{i,0} (C_{i,1}/C_{i,0} - 2)² = (1/2)(0 + 40/11 + 40/9) = 400/99`. -/
theorem Cex_sigma2_0 : sigma2 Cex 4 0 = 400 / 99 := by
  simp only [sigma2, Cex_contributors0, Cex_fhat0, F]
  simp [Cex]
  norm_num

theorem Cex_sigma2_1 : sigma2 Cex 4 1 = 1 / 4 := by
  simp only [sigma2, Cex_contributors1, Cex_fhat1, F]
  simp [Cex]
  norm_num

/-- With a single contributing accident year the divisor `n - k - 2` is `0`, and
`1 / 0 = 0` in Lean: the last-period variance is not estimable and the
definition returns `0` (Mack extrapolates it instead; see `Msep.lean`). -/
theorem Cex_sigma2_2 : sigma2 Cex 4 2 = 0 := by
  simp only [sigma2]; norm_num

theorem Cex_relVar0 : relVar Cex 4 0 = 1 / 297 := by
  rw [relVar, Cex_sigma2_0, Cex_fhat0, Cex_S0]; norm_num
theorem Cex_relVar1 : relVar Cex 4 1 = 1 / 2809 := by
  rw [relVar, Cex_sigma2_1, Cex_fhat1, Cex_S1]; norm_num
theorem Cex_relVar2 : relVar Cex 4 2 = 0 := by
  rw [relVar, Cex_sigma2_2]; simp

theorem Cex_ultimate_pos : 0 < ultimate Cex 4 3 := by
  simp only [ultimate, Chat]
  rw [show (4 : ℕ) - 1 - 3 = 0 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
    show Ico 0 3 = {0, 1, 2} from by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton,
    Cex_fhat0, Cex_fhat1, Cex_fhat2]
  simp [Cex]

/-- **Strict counterexample.** On the triangle `Cex`, for the youngest accident
year, the conditional-resampling estimation-error term strictly exceeds Mack's. -/
theorem mackEstimation_lt_bbmwEstimation_Cex :
    mackEstimation Cex 4 3 < bbmwEstimation Cex 4 3 := by
  have hdiff := bbmwEstimation_sub_mackEstimation Cex 4 3
  rw [show (4 : ℕ) - 1 - 3 = 0 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
    show Ico 0 3 = {0, 1, 2} from by decide] at hdiff
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton,
    sum_insert (by decide), sum_insert (by decide), sum_singleton,
    Cex_relVar0, Cex_relVar1, Cex_relVar2] at hdiff
  have hpos : 0 < (ultimate Cex 4 3) ^ 2 := by
    have := Cex_ultimate_pos; positivity
  have hrem : (0 : ℝ) < (1 + 1 / 297) * ((1 + 1 / 2809) * (1 + 0)) - 1 - (1 / 297 + (1 / 2809 + 0)) := by
    norm_num
  have : 0 < bbmwEstimation Cex 4 3 - mackEstimation Cex 4 3 := by
    rw [hdiff]; exact mul_pos hpos hrem
  linarith

/-- **Existence form.** There is a run-off triangle and an accident year on which
Mack's estimation-error estimator and the conditional-resampling estimator differ. -/
theorem exists_mackEstimation_lt_bbmwEstimation :
    ∃ (C : ℕ → ℕ → ℝ) (n i : ℕ), mackEstimation C n i < bbmwEstimation C n i :=
  ⟨Cex, 4, 3, mackEstimation_lt_bbmwEstimation_Cex⟩

end

end VerifiedReserving
