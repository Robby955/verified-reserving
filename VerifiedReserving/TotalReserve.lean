import VerifiedReserving.Catalogue

/-!
# The total reserve: Mack's Corollary and its conditional-resampling counterpart

Mack (1993), Corollary to Theorem 3, estimates the MSEP of the total reserve
`R̂ = ∑_i R̂_i` by

`∑_i msep_i + ∑_i Ĉ_{i,n-1} (∑_{j>i} Ĉ_{j,n-1}) ∑_{k=d_i}^{n-2} 2 σ̂_k² / (f̂_k² S_k)`,

the cross terms running over the development factors of the older accident
year `i` (its remaining row is the shorter one and is shared with every
younger year `j > i`). In the notation of `Catalogue.lean`, with
`a_k = σ̂_k²/(f̂_k² S_k)`, the cross term of the pair `(i, j)` is
`2 Ĉ_i Ĉ_j ∑_{k ∈ row i} a_k`.

Buchwalder, Bühlmann, Merz and Wüthrich (2006, Section 4.3) aggregate the
conditional-resampling estimator with the analogous cross term
`2 Ĉ_i Ĉ_j (∏_{k ∈ row i} (1 + a_k) - 1)`.

Proved here, deterministically: the aggregated estimation-error terms differ
by `∑_i (Ĉ_i² + 2 Ĉ_i ∑_{j>i} Ĉ_j) · (∏_{k ∈ row i}(1 + a_k) - 1 - ∑_{k ∈ row i} a_k)`,
so with nonnegative ultimates and `a_k ≥ 0` the resampling total is at least
Mack's total, and the excess is the same second-order remainder as in the
single-year case, row by row. The reference computation uses `msepTotal`
below to reproduce the 13 percent total standard error of Mack (1993).
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- The remaining-row relative estimation variances of accident year `i`, summed. -/
def rowSum (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := ∑ k ∈ Ico (n - 1 - i) (n - 1), relVar C n k

/-- The remaining-row product `∏ (1 + a_k) - 1` of accident year `i`. -/
def rowProd (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := ∏ k ∈ Ico (n - 1 - i) (n - 1), (1 + relVar C n k) - 1

/-- Sum of the projected ultimates of the accident years younger than `i`. -/
def laterUltimates (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := ∑ j ∈ Ico (i + 1) n, ultimate C n j

/-- Mack's cross term for accident year `i` against all younger years. -/
def mackCross (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  ultimate C n i * laterUltimates C n i * (2 * rowSum C n i)

/-- The conditional-resampling cross term (BBMW 2006, Section 4.3). -/
def bbmwCross (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  ultimate C n i * laterUltimates C n i * (2 * rowProd C n i)

/-- **Mack's Corollary.** The estimator of the MSEP of the total reserve. -/
def msepTotal (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, msep C n i + ∑ i ∈ range n, mackCross C n i

/-- Mack's aggregated estimation-error term (the part of `msepTotal` that is
not process variance). -/
def mackTotalEstimation (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, mackEstimation C n i + ∑ i ∈ range n, mackCross C n i

/-- The aggregated conditional-resampling estimation-error term. -/
def bbmwTotalEstimation (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, bbmwEstimation C n i + ∑ i ∈ range n, bbmwCross C n i

theorem mackEstimation_eq_rowSum (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    mackEstimation C n i = (ultimate C n i) ^ 2 * rowSum C n i := rfl

theorem bbmwEstimation_eq_rowProd (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    bbmwEstimation C n i = (ultimate C n i) ^ 2 * rowProd C n i := rfl

/-- **The aggregated difference is the row-wise remainder, weighted by the ultimates.** -/
theorem bbmwTotalEstimation_sub_mackTotalEstimation (C : ℕ → ℕ → ℝ) (n : ℕ) :
    bbmwTotalEstimation C n - mackTotalEstimation C n
      = ∑ i ∈ range n,
          ((ultimate C n i) ^ 2 + 2 * ultimate C n i * laterUltimates C n i)
            * (rowProd C n i - rowSum C n i) := by
  unfold bbmwTotalEstimation mackTotalEstimation
  simp only [bbmwEstimation_eq_rowProd, mackEstimation_eq_rowSum, bbmwCross, mackCross]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The row remainder is nonnegative when the relative estimation variances are. -/
theorem rowProd_sub_rowSum_nonneg (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (ha : ∀ k ∈ Ico (n - 1 - i) (n - 1), 0 ≤ relVar C n k) :
    0 ≤ rowProd C n i - rowSum C n i := by
  unfold rowProd rowSum
  have := remainder_nonneg _ _ ha
  linarith

/-- **Mack's total ≤ the resampling total** with nonnegative ultimates and
relative estimation variances. -/
theorem mackTotalEstimation_le_bbmwTotalEstimation (C : ℕ → ℕ → ℝ) (n : ℕ)
    (hU : ∀ i ∈ range n, 0 ≤ ultimate C n i)
    (ha : ∀ k, 0 ≤ relVar C n k) :
    mackTotalEstimation C n ≤ bbmwTotalEstimation C n := by
  have h := bbmwTotalEstimation_sub_mackTotalEstimation C n
  have hnn : 0 ≤ ∑ i ∈ range n,
      ((ultimate C n i) ^ 2 + 2 * ultimate C n i * laterUltimates C n i)
        * (rowProd C n i - rowSum C n i) := by
    refine sum_nonneg fun i hi => ?_
    have h1 : 0 ≤ laterUltimates C n i := by
      unfold laterUltimates
      refine sum_nonneg fun j hj => hU j ?_
      have := (mem_Ico.mp hj).2
      exact mem_range.mpr this
    have h2 := rowProd_sub_rowSum_nonneg C n i (fun k _ => ha k)
    have h3 := hU i hi
    have h4 : 0 ≤ (ultimate C n i) ^ 2 + 2 * ultimate C n i * laterUltimates C n i := by positivity
    exact mul_nonneg h4 h2
  linarith

end

end VerifiedReserving
