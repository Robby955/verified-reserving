import VerifiedReserving.ChainLadder

/-!
# Mack's moment-matched lognormal approximation

This file formalizes the parameter conversion in Thomas Mack, "Measuring the
Variability of Chain Ladder Reserve Estimates," CAS Forum, Spring 1994,
Chapter 4, equation (10), pp. 118-119. The paper uses the conversion to form a
lognormal approximation to the reserve distribution. The two results below
verify the mean and variance algebra; they do not assert that a reserve is
lognormally distributed.
-/

namespace VerifiedReserving

noncomputable section

/-- The log-variance parameter matched to arithmetic mean `m` and variance
`v`, Mack (1994), Chapter 4, equation (10), p. 119. -/
def mackLognormalSigma2 (m v : ℝ) : ℝ :=
  Real.log (1 + v / m ^ 2)

/-- The log-mean parameter matched to arithmetic mean `m` and variance `v`,
Mack (1994), Chapter 4, equation (10), p. 119. -/
def mackLognormalMu (m v : ℝ) : ℝ :=
  Real.log m - mackLognormalSigma2 m v / 2

/-- The lognormal mean formula at Mack's matched parameters equals `m` when
`m` is positive, Mack (1994), Chapter 4, equation (10), p. 119. -/
theorem mackLognormal_mean_eq (m v : ℝ) (hm : 0 < m) :
    Real.exp (mackLognormalMu m v + mackLognormalSigma2 m v / 2) = m := by
  unfold mackLognormalMu
  have h :
      Real.log m - mackLognormalSigma2 m v / 2 +
          mackLognormalSigma2 m v / 2 = Real.log m := by
    ring
  rw [h, Real.exp_log hm]

/-- The lognormal variance formula at Mack's matched parameters equals `v`
when `m` is positive and `v` is nonnegative, Mack (1994), Chapter 4,
equation (10), p. 119. -/
theorem mackLognormal_variance_eq
    (m v : ℝ) (hm : 0 < m) (hv : 0 ≤ v) :
    Real.exp (2 * mackLognormalMu m v + mackLognormalSigma2 m v) *
        (Real.exp (mackLognormalSigma2 m v) - 1) = v := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have harg : 0 < 1 + v / m ^ 2 := by positivity
  unfold mackLognormalMu mackLognormalSigma2
  have hcenter :
      2 * (Real.log m - Real.log (1 + v / m ^ 2) / 2) +
          Real.log (1 + v / m ^ 2) = Real.log m + Real.log m := by
    ring
  rw [hcenter, Real.exp_add, Real.exp_log hm, Real.exp_log harg]
  field_simp
  ring

end

end VerifiedReserving
