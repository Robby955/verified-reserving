import Mathlib

/-!
# Chain-ladder estimators on a run-off triangle

Deterministic layer of Mack's distribution-free chain-ladder model
(Mack, ASTIN Bulletin 23 (1993) 213-225).

A run-off triangle with `n` accident years and `n` development years is a
function `C : ℕ → ℕ → ℝ` giving cumulative claims `C i k` for accident year
`i` and development year `k` (both zero-based). Entries with `i + k ≤ n - 1`
are observed.

This file defines the chain-ladder development factors, Mack's variance
estimators, the chain-ladder ultimate and reserve, and Mack's mean squared
error of prediction (MSEP) formula, and proves the deterministic identities
used in Mack's derivation. No probabilistic assumption is used here; the
stochastic layer (Mack's three assumptions and the unbiasedness and MSEP
theorems) is a separate file.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- Accident years that contribute to the development factor `k → k+1`:
`i = 0, …, n-k-2`, i.e. those with `C i (k+1)` observed. -/
def contributors (n k : ℕ) : Finset ℕ := range (n - k - 1)

/-- Column sum `S_k = ∑_{i ≤ n-k-2} C_{i,k}` (the denominator of `f̂_k`). -/
def S (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := ∑ i ∈ contributors n k, C i k

/-- Shifted column sum `T_k = ∑_{i ≤ n-k-2} C_{i,k+1}` (the numerator of `f̂_k`). -/
def T (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := ∑ i ∈ contributors n k, C i (k + 1)

/-- Chain-ladder development factor `f̂_k = T_k / S_k`. -/
def fhat (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ := T C n k / S C n k

/-- Individual development factor `F_{i,k} = C_{i,k+1} / C_{i,k}`. -/
def F (C : ℕ → ℕ → ℝ) (i k : ℕ) : ℝ := C i (k + 1) / C i k

/-- Mack's variance estimator
`σ̂_k² = (n-k-2)⁻¹ ∑_{i ≤ n-k-2} C_{i,k} (F_{i,k} - f̂_k)²`. -/
def sigma2 (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  (1 / ((n : ℝ) - k - 2)) * ∑ i ∈ contributors n k, C i k * (F C i k - fhat C n k) ^ 2

/-- Chain-ladder projection of accident year `i` to development year `k`,
starting from the latest observed entry `C_{i, n-1-i}`. -/
def Chat (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  C i (n - 1 - i) * ∏ j ∈ Ico (n - 1 - i) k, fhat C n j

/-- Chain-ladder ultimate `Ĉ_{i,n-1}`. -/
def ultimate (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := Chat C n i (n - 1)

/-- Chain-ladder reserve `R̂_i = Ĉ_{i,n-1} - C_{i,n-1-i}`. -/
def reserve (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := ultimate C n i - C i (n - 1 - i)

/-- Mack's estimator of the mean squared error of prediction of `R̂_i`
(Mack 1993, Theorem 3):
`msep_i = Ĉ_{i,n-1}² ∑_{k = n-1-i}^{n-2} (σ̂_k² / f̂_k²) (1 / Ĉ_{i,k} + 1 / S_k)`. -/
def msep (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 *
    ∑ k ∈ Ico (n - 1 - i) (n - 1),
      (sigma2 C n k / (fhat C n k) ^ 2) * (1 / Chat C n i k + 1 / S C n k)

/-! ## Deterministic identities -/

/-- `f̂_k` is the `C_{i,k}`-weighted average of the individual factors `F_{i,k}`
(Mack 1993, eq. (2)). Division by zero is `0` in Lean, so no hypothesis on
`S_k` is needed; only the individual denominators must be nonzero. -/
theorem fhat_eq_weighted_average (C : ℕ → ℕ → ℝ) (n k : ℕ)
    (h : ∀ i ∈ contributors n k, C i k ≠ 0) :
    fhat C n k = ∑ i ∈ contributors n k, (C i k / S C n k) * F C i k := by
  unfold fhat T F
  rw [sum_div]
  refine sum_congr rfl (fun i hi => ?_)
  rw [div_mul_div_comm, mul_comm (C i k) (C i (k + 1)), mul_div_mul_right _ _ (h i hi)]

/-- The shifted column sum is the weighted sum of individual factors. -/
theorem T_eq_sum_weighted_F (C : ℕ → ℕ → ℝ) (n k : ℕ)
    (h : ∀ i ∈ contributors n k, C i k ≠ 0) :
    T C n k = ∑ i ∈ contributors n k, C i k * F C i k := by
  unfold T F
  refine sum_congr rfl (fun i hi => ?_)
  rw [mul_div_cancel₀ _ (h i hi)]

/-- Weighted sum-of-squares decomposition around an arbitrary centre `f`:
`∑ C_{i,k} (F_{i,k} - f)² = ∑ C_{i,k} F_{i,k}² - 2 f T_k + f² S_k`. -/
theorem weighted_sq_dev (C : ℕ → ℕ → ℝ) (n k : ℕ) (f : ℝ)
    (h : ∀ i ∈ contributors n k, C i k ≠ 0) :
    ∑ i ∈ contributors n k, C i k * (F C i k - f) ^ 2
      = (∑ i ∈ contributors n k, C i k * (F C i k) ^ 2) - 2 * f * T C n k + f ^ 2 * S C n k := by
  rw [T_eq_sum_weighted_F C n k h]
  unfold S
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  ring

/-- At the chain-ladder centre `f = f̂_k` the cross term collapses:
`∑ C_{i,k} (F_{i,k} - f̂_k)² = ∑ C_{i,k} F_{i,k}² - S_k f̂_k²`.
This is the identity behind the `(n-k-2)` degrees of freedom in `σ̂_k²`. -/
theorem weighted_sq_dev_at_fhat (C : ℕ → ℕ → ℝ) (n k : ℕ)
    (h : ∀ i ∈ contributors n k, C i k ≠ 0) (hS : S C n k ≠ 0) :
    ∑ i ∈ contributors n k, C i k * (F C i k - fhat C n k) ^ 2
      = (∑ i ∈ contributors n k, C i k * (F C i k) ^ 2) - S C n k * (fhat C n k) ^ 2 := by
  rw [weighted_sq_dev C n k _ h]
  unfold fhat
  field_simp
  ring

/-- One chain-ladder step: `Ĉ_{i,k+1} = Ĉ_{i,k} f̂_k` for `k ≥ n-1-i`. -/
theorem Chat_succ (C : ℕ → ℕ → ℝ) (n i k : ℕ) (hk : n - 1 - i ≤ k) :
    Chat C n i (k + 1) = Chat C n i k * fhat C n k := by
  unfold Chat
  rw [prod_Ico_succ_top hk, mul_assoc]

/-- The projection starts at the latest observed entry. -/
theorem Chat_diag (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    Chat C n i (n - 1 - i) = C i (n - 1 - i) := by
  unfold Chat
  simp

/-- The oldest accident year is fully developed: its chain-ladder reserve is zero. -/
theorem reserve_zero_of_oldest (C : ℕ → ℕ → ℝ) (n : ℕ) :
    reserve C n 0 = 0 := by
  unfold reserve ultimate Chat
  simp

end

end VerifiedReserving
