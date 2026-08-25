import VerifiedReserving.ChainLadder

/-!
# Bühlmann-Straub credibility

Bühlmann and Straub, "Glaubwürdigkeit für Schadensätze" (1970), derive the
credibility estimator for exposure-weighted observations. Their Section 6,
pp. 118-120, minimizes expected squared prediction error over unbiased linear
estimators and obtains the normal equations in display (1). Their display (4),
p. 123, writes the one-risk estimator as

`Z * weightedMean + (1 - Z) * collectiveMean`,
`Z = totalWeight * betweenVariance /
  (processVariance + totalWeight * betweenVariance)`.

The deterministic quadratic loss below is an algebraic representation of the
one-risk normal equation. It is not asserted to be the sample objective used in
the paper. Completing its square proves the same closed-form estimator
minimizes it when the total quadratic coefficient is positive. The variance
components and collective mean remain inputs; no theorem estimates them.
-/

open Finset

namespace VerifiedReserving

noncomputable section

variable {ι : Type*}

/-- Total exposure weight `P_·k` in Bühlmann-Straub (1970), display (4),
p. 123. -/
def buhlmannStraubTotalWeight (sample : Finset ι) (weight : ι → ℝ) : ℝ :=
  ∑ i ∈ sample, weight i

/-- Exposure-weighted observation total `∑_l P_l X_l`, the numerator of the
individual mean in Bühlmann-Straub (1970), display (4), p. 123. -/
def buhlmannStraubWeightedTotal
    (sample : Finset ι) (weight observation : ι → ℝ) : ℝ :=
  ∑ i ∈ sample, weight i * observation i

/-- Exposure-weighted individual mean `X̄ = ∑_l P_l X_l / P_·`, from
Bühlmann-Straub (1970), display (4), p. 123. -/
def buhlmannStraubWeightedMean
    (sample : Finset ι) (weight observation : ι → ℝ) : ℝ :=
  buhlmannStraubWeightedTotal sample weight observation /
    buhlmannStraubTotalWeight sample weight

/-- Credibility factor `Z = P_· w / (v + P_· w)` from Bühlmann-Straub
(1970), display (4), p. 123. Here `processVariance` is `v` and
`betweenVariance` is the paper's structural parameter `w`. -/
def buhlmannStraubCredibility
    (totalWeight processVariance betweenVariance : ℝ) : ℝ :=
  totalWeight * betweenVariance /
    (processVariance + totalWeight * betweenVariance)

/-- Closed-form Bühlmann-Straub estimate, written without separately dividing
by the total exposure. This is algebraically the display (4) form
`Z X̄ + (1-Z) m`. -/
def buhlmannStraubEstimate
    (sample : Finset ι) (weight observation : ι → ℝ)
    (collectiveMean processVariance betweenVariance : ℝ) : ℝ :=
  (betweenVariance * buhlmannStraubWeightedTotal sample weight observation
      + processVariance * collectiveMean) /
    (processVariance
      + buhlmannStraubTotalWeight sample weight * betweenVariance)

/-- A deterministic penalized quadratic whose first-order equation is the
one-risk Bühlmann-Straub normal equation. This is an algebraic representation,
not the expected prediction-error objective used in Section 6 of the paper. -/
def buhlmannStraubLoss
    (sample : Finset ι) (weight observation : ι → ℝ)
    (collectiveMean processVariance betweenVariance candidate : ℝ) : ℝ :=
  betweenVariance *
      ∑ i ∈ sample, weight i * (observation i - candidate) ^ 2
    + processVariance * (candidate - collectiveMean) ^ 2

/-- Weighted sum-of-squares decomposition around an arbitrary candidate. This
is the deterministic identity underlying the one-risk normal equation in
Bühlmann-Straub (1970), display (1), p. 120. -/
theorem buhlmannStraub_weighted_sq_dev
    (sample : Finset ι) (weight observation : ι → ℝ) (candidate : ℝ) :
    ∑ i ∈ sample, weight i * (observation i - candidate) ^ 2 =
      (∑ i ∈ sample, weight i * observation i ^ 2)
        - 2 * candidate * buhlmannStraubWeightedTotal sample weight observation
        + candidate ^ 2 * buhlmannStraubTotalWeight sample weight := by
  unfold buhlmannStraubWeightedTotal buhlmannStraubTotalWeight
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The closed-form estimate solves the one-risk Bühlmann-Straub normal
equation, the specialization of display (1), p. 120. -/
theorem buhlmannStraubEstimate_normal_eq
    (sample : Finset ι) (weight observation : ι → ℝ)
    (collectiveMean processVariance betweenVariance : ℝ)
    (hden : processVariance
      + buhlmannStraubTotalWeight sample weight * betweenVariance ≠ 0) :
    (processVariance
        + buhlmannStraubTotalWeight sample weight * betweenVariance) *
        buhlmannStraubEstimate sample weight observation collectiveMean
          processVariance betweenVariance =
      betweenVariance * buhlmannStraubWeightedTotal sample weight observation
        + processVariance * collectiveMean := by
  unfold buhlmannStraubEstimate
  field_simp

/-- Square completion of the deterministic loss around the closed-form
estimate. Its coefficient is the left side of the one-risk normal equation. -/
theorem buhlmannStraubLoss_eq_at_estimate_add
    (sample : Finset ι) (weight observation : ι → ℝ)
    (collectiveMean processVariance betweenVariance candidate : ℝ)
    (hden : processVariance
      + buhlmannStraubTotalWeight sample weight * betweenVariance ≠ 0) :
    buhlmannStraubLoss sample weight observation collectiveMean
        processVariance betweenVariance candidate =
      buhlmannStraubLoss sample weight observation collectiveMean
          processVariance betweenVariance
          (buhlmannStraubEstimate sample weight observation collectiveMean
            processVariance betweenVariance)
        + (processVariance
            + buhlmannStraubTotalWeight sample weight * betweenVariance) *
          (candidate - buhlmannStraubEstimate sample weight observation collectiveMean
            processVariance betweenVariance) ^ 2 := by
  unfold buhlmannStraubLoss
  rw [buhlmannStraub_weighted_sq_dev, buhlmannStraub_weighted_sq_dev]
  have hnormal := buhlmannStraubEstimate_normal_eq sample weight observation
    collectiveMean processVariance betweenVariance hden
  linear_combination 2 *
    (candidate - buhlmannStraubEstimate sample weight observation collectiveMean
      processVariance betweenVariance) * hnormal

/-- The Bühlmann-Straub estimate minimizes the deterministic quadratic when
its total quadratic coefficient is positive. -/
theorem buhlmannStraubEstimate_minimizes
    (sample : Finset ι) (weight observation : ι → ℝ)
    (collectiveMean processVariance betweenVariance candidate : ℝ)
    (hpos : 0 < processVariance
      + buhlmannStraubTotalWeight sample weight * betweenVariance) :
    buhlmannStraubLoss sample weight observation collectiveMean
        processVariance betweenVariance
        (buhlmannStraubEstimate sample weight observation collectiveMean
          processVariance betweenVariance) ≤
      buhlmannStraubLoss sample weight observation collectiveMean
        processVariance betweenVariance candidate := by
  rw [buhlmannStraubLoss_eq_at_estimate_add sample weight observation
    collectiveMean processVariance betweenVariance candidate hpos.ne']
  exact le_add_of_nonneg_right (mul_nonneg hpos.le (sq_nonneg _))

/-- The closed-form estimate is the credibility-weighted blend in
Bühlmann-Straub (1970), display (4), p. 123. -/
theorem buhlmannStraubEstimate_eq_credibility
    (sample : Finset ι) (weight observation : ι → ℝ)
    (collectiveMean processVariance betweenVariance : ℝ)
    (hweight : buhlmannStraubTotalWeight sample weight ≠ 0)
    (hden : processVariance
      + buhlmannStraubTotalWeight sample weight * betweenVariance ≠ 0) :
    buhlmannStraubEstimate sample weight observation collectiveMean
        processVariance betweenVariance =
      buhlmannStraubCredibility
          (buhlmannStraubTotalWeight sample weight) processVariance betweenVariance *
        buhlmannStraubWeightedMean sample weight observation
        + (1 - buhlmannStraubCredibility
          (buhlmannStraubTotalWeight sample weight) processVariance betweenVariance) *
      collectiveMean := by
  have hden' : betweenVariance * buhlmannStraubTotalWeight sample weight
      + processVariance ≠ 0 := by
    simpa [add_comm, mul_comm] using hden
  unfold buhlmannStraubEstimate buhlmannStraubCredibility
    buhlmannStraubWeightedMean
  field_simp [hweight]
  have hinv :
      (betweenVariance * buhlmannStraubTotalWeight sample weight + processVariance) *
          (betweenVariance * buhlmannStraubTotalWeight sample weight + processVariance)⁻¹ = 1 :=
    mul_inv_cancel₀ hden'
  linear_combination collectiveMean * hinv

/-- With nonnegative exposure and variance components and a positive
denominator, the credibility factor in display (4), p. 123, lies in `[0,1]`. -/
theorem buhlmannStraubCredibility_mem_Icc
    (totalWeight processVariance betweenVariance : ℝ)
    (hweight : 0 ≤ totalWeight) (hprocess : 0 ≤ processVariance)
    (hbetween : 0 ≤ betweenVariance)
    (hden : 0 < processVariance + totalWeight * betweenVariance) :
    buhlmannStraubCredibility totalWeight processVariance betweenVariance ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (mul_nonneg hweight hbetween) hden.le
  · rw [buhlmannStraubCredibility, div_le_one hden]
    linarith

end

end VerifiedReserving
