import VerifiedReserving.Msep

/-!
# The variant catalogue: Mack's estimation-error term versus the
# conditional-resampling (BBMW) term

Write `a_k = σ̂_k² / (f̂_k² S_k)` for the relative estimation variance of the
development factor `k` along the row of accident year `i`. Two published
estimators of the estimation-error part of the MSEP are in use:

* Mack (1993): `Ĉ_{i,n-1}² ∑_k a_k` (`mackEstimation`);
* Buchwalder, Bühlmann, Merz and Wüthrich (2006), the conditional-resampling
  form, also the one Murphy (1994) arrives at: `Ĉ_{i,n-1}² (∏_k (1 + a_k) - 1)`
  (`bbmwEstimation`).

Facts proved here, all deterministic:

1. `∏_k (1 + a_k) - 1 = ∑_k a_k + R` with `R ≥ 0` whenever every `a_k ≥ 0`
   (Weierstrass product inequality), so `mackEstimation ≤ bbmwEstimation`.
2. For two development periods the remainder is exactly the pairwise product:
   `(1+a)(1+b) - 1 - (a+b) = a b`.
3. `R = 0` when at most one `a_k` is nonzero: the two estimators coincide
   exactly when there is at most one uncertain development factor.
4. Upper bound `∏ (1 + a_k) ≤ exp(∑ a_k)`: the disagreement is second order
   in the relative estimation variances, which is why the two estimators are
   numerically close on typical triangles (Buchwalder et al. 2006, Table 5)
   and why Buchwalder et al. and Wüthrich and Merz (2008, Remark 3.13)
   describe Mack's term as the linear approximation from below of theirs.
   For two development factors the remainder `a_1 a_2` appears in Mack,
   Quarg and Braun (2006, p. 552); the general closed form is proved here.
   In R's `ChainLadder`, `mse.method = "Mack"` implements the sum and
   `mse.method = "Independence"` the product.

`a_k ≥ 0` holds whenever the triangle entries are nonnegative, since `σ̂_k²`
is then a nonnegative weighted sum of squares and `S_k ≥ 0`.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- Relative estimation variance of development factor `k`: `σ̂_k² / (f̂_k² S_k)`. -/
def relVar (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  sigma2 C n k / (fhat C n k) ^ 2 / S C n k

/-- The BBMW / conditional-resampling estimator of the estimation error. -/
def bbmwEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 * (∏ k ∈ Ico (n - 1 - i) (n - 1), (1 + relVar C n k) - 1)

theorem mackEstimation_eq_sum_relVar (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    mackEstimation C n i = (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), relVar C n k := by
  rfl

/-! ## The product-minus-sum remainder -/

/-- Weierstrass product inequality: `1 + ∑ a ≤ ∏ (1 + a)` for nonnegative `a`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ k ∈ s, 0 ≤ a k) :
    1 + ∑ k ∈ s, a k ≤ ∏ k ∈ s, (1 + a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun k hk => ha k (mem_insert_of_mem hk))
    have haj : 0 ≤ a j := ha j (mem_insert_self _ _)
    have hsum : 0 ≤ ∑ k ∈ s, a k := sum_nonneg (fun k hk => ha k (mem_insert_of_mem hk))
    nlinarith [mul_nonneg haj hsum, mul_nonneg haj (by linarith : (0 : ℝ) ≤ ∏ k ∈ s, (1 + a k) - 1 - ∑ k ∈ s, a k)]

/-- The remainder `∏ (1 + a) - 1 - ∑ a` is nonnegative for nonnegative `a`. -/
theorem remainder_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ k ∈ s, 0 ≤ a k) :
    0 ≤ ∏ k ∈ s, (1 + a k) - 1 - ∑ k ∈ s, a k := by
  have := one_add_sum_le_prod_one_add s a ha
  linarith

/-- Two periods: the remainder is exactly the pairwise product. -/
theorem remainder_two (a b : ℝ) : (1 + a) * (1 + b) - 1 - (a + b) = a * b := by ring

/-- If at most one term is nonzero the remainder vanishes: the two estimators agree. -/
theorem remainder_eq_zero_of_subsingleton_support {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h : ∀ j ∈ s, ∀ k ∈ s, a j ≠ 0 → a k ≠ 0 → j = k) :
    ∏ k ∈ s, (1 + a k) - 1 - ∑ k ∈ s, a k = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have h' : ∀ j' ∈ s, ∀ k ∈ s, a j' ≠ 0 → a k ≠ 0 → j' = k :=
      fun j' hj' k hk => h j' (mem_insert_of_mem hj') k (mem_insert_of_mem hk)
    have ih' := ih h'
    by_cases haj : a j = 0
    · rw [haj]; linarith
    · -- every other term in `s` is zero
      have hzero : ∀ k ∈ s, a k = 0 := by
        intro k hk
        by_contra hk0
        have := h j (mem_insert_self _ _) k (mem_insert_of_mem hk) haj hk0
        exact hj (this ▸ hk)
      have hprod : ∏ k ∈ s, (1 + a k) = 1 := by
        refine prod_eq_one (fun k hk => ?_); rw [hzero k hk]; ring
      have hsum : ∑ k ∈ s, a k = 0 := sum_eq_zero hzero
      rw [hprod, hsum]; ring

/-- Second-order bound: `∏ (1 + a) ≤ exp (∑ a)`, hence
`∏ (1 + a) - 1 - ∑ a ≤ exp (∑ a) - 1 - ∑ a`. -/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ k ∈ s, 0 ≤ a k) :
    ∏ k ∈ s, (1 + a k) ≤ Real.exp (∑ k ∈ s, a k) := by
  rw [Real.exp_sum]
  refine prod_le_prod (fun k hk => by linarith [ha k hk]) (fun k _ => ?_)
  linarith [Real.add_one_le_exp (a k)]

/-! ## The catalogue rows -/

/-- **Mack ≤ BBMW.** With nonnegative relative estimation variances, Mack's
estimation-error term is at most the conditional-resampling term. -/
theorem mackEstimation_le_bbmwEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (ha : ∀ k ∈ Ico (n - 1 - i) (n - 1), 0 ≤ relVar C n k) :
    mackEstimation C n i ≤ bbmwEstimation C n i := by
  rw [mackEstimation_eq_sum_relVar, bbmwEstimation]
  have := remainder_nonneg _ _ ha
  have hsq : 0 ≤ (ultimate C n i) ^ 2 := sq_nonneg _
  nlinarith

/-- **The exact difference.** `bbmw - mack = Ĉ² · (∏ (1 + a_k) - 1 - ∑ a_k)`. -/
theorem bbmwEstimation_sub_mackEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    bbmwEstimation C n i - mackEstimation C n i
      = (ultimate C n i) ^ 2 *
          (∏ k ∈ Ico (n - 1 - i) (n - 1), (1 + relVar C n k) - 1 - ∑ k ∈ Ico (n - 1 - i) (n - 1), relVar C n k) := by
  rw [mackEstimation_eq_sum_relVar, bbmwEstimation]; ring

/-- **Agreement.** For the second-latest accident year (one development factor
along the row) the two estimators coincide. -/
theorem bbmwEstimation_eq_mackEstimation_of_one_factor (C : ℕ → ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    bbmwEstimation C n 1 = mackEstimation C n 1 := by
  have hI : Ico (n - 1 - 1) (n - 1) = {n - 2} := by
    have h1 : n - 1 - 1 = n - 2 := by omega
    have h2 : n - 1 = n - 2 + 1 := by omega
    rw [h1, h2, Nat.Ico_succ_singleton]
  rw [bbmwEstimation, mackEstimation_eq_sum_relVar, hI]
  simp

/-- **Second-order bound on the disagreement.**
`bbmw - mack ≤ Ĉ² (exp(∑ a_k) - 1 - ∑ a_k)`. -/
theorem bbmwEstimation_sub_mackEstimation_le (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (ha : ∀ k ∈ Ico (n - 1 - i) (n - 1), 0 ≤ relVar C n k) :
    bbmwEstimation C n i - mackEstimation C n i
      ≤ (ultimate C n i) ^ 2 *
          (Real.exp (∑ k ∈ Ico (n - 1 - i) (n - 1), relVar C n k) - 1 - ∑ k ∈ Ico (n - 1 - i) (n - 1), relVar C n k) := by
  rw [bbmwEstimation_sub_mackEstimation]
  have := prod_one_add_le_exp_sum _ _ ha
  have hsq : 0 ≤ (ultimate C n i) ^ 2 := sq_nonneg _
  nlinarith

end

end VerifiedReserving
