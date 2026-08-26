import VerifiedReserving.Rohr

/-!
# Röhr's arbitrary-horizon error-propagation formulas

Ancus Röhr's CAE 2014 presentation, *Chain Ladder and Error Propagation*,
slide 13, gives the following approximation formulas:

`MSEP / X̂² ≈ ∑_j û_j² q̂_j`

and, for the claims development result over the next `k` years,

`MSEP(CDR_k) / X̂² ≈ ∑_j û_j² (q̂_j - q̂_{j-k}) / (1 - q̂_{j-k})`.

Here `û_j²` is already a squared relative uncertainty and `q̂_j` is the
influence of development factor `j` on the predicted ultimate. The slide sets
`q̂_j = 0` below its active index range. Slide 17 splits the second summand
algebraically into

`û_j² (1-q̂_j)(q̂_j-q̂_{j-k})/(1-q̂_{j-k})²`

and

`û_j² ((q̂_j-q̂_{j-k})/(1-q̂_{j-k}))²`,

labeled process and parameter error in the presentation.

This module records the displayed approximation formulas as definitions and
proves only their exact algebra. It does not define the derivative that
produces `q̂`, identify these expressions with a stochastic MSEP, or attribute the
formulas to the full 2016 paper. The finite set `s` is the set of development
indices included in a particular application.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-! ## The two displayed approximation formulas -/

/-- Röhr's slide-13 approximation for ultimate relative MSEP,
`∑_j û_j² q̂_j`. This is a definition because the source display is an
approximation. -/
def rohrUltimateRelMsepApprox (s : Finset ℕ) (uSq q : ℕ → ℝ) : ℝ :=
  ∑ j ∈ s, uSq j * q j

/-- The process part of the ultimate-horizon split on slide 17,
`∑_j û_j² (1-q̂_j)q̂_j`. -/
def rohrUltimateProcessRelApprox (s : Finset ℕ) (uSq q : ℕ → ℝ) : ℝ :=
  ∑ j ∈ s, uSq j * ((1 - q j) * q j)

/-- The parameter part of the ultimate-horizon split on slide 17,
`∑_j û_j² q̂_j²`. -/
def rohrUltimateParameterRelApprox (s : Finset ℕ) (uSq q : ℕ → ℝ) : ℝ :=
  ∑ j ∈ s, uSq j * (q j) ^ 2

/-- The horizon weight `(q̂_j-q̂_{j-k})/(1-q̂_{j-k})` from slide 13.
`qNow` and `qPast` are kept separate so the algebra does not depend on an
indexing convention. -/
def rohrHorizonWeight (qNow qPast : ℝ) : ℝ :=
  (qNow - qPast) / (1 - qPast)

/-- One summand of Röhr's arbitrary-horizon relative-MSEP approximation. -/
def rohrHorizonTerm (uSq qNow qPast : ℝ) : ℝ :=
  uSq * rohrHorizonWeight qNow qPast

/-- The process part of one arbitrary-horizon summand on slide 17. -/
def rohrHorizonProcessTerm (uSq qNow qPast : ℝ) : ℝ :=
  uSq * ((1 - qNow) * (qNow - qPast) / (1 - qPast) ^ 2)

/-- The parameter part of one arbitrary-horizon summand on slide 17. -/
def rohrHorizonParameterTerm (uSq qNow qPast : ℝ) : ℝ :=
  uSq * ((qNow - qPast) / (1 - qPast)) ^ 2

/-- Röhr's slide-13 arbitrary-horizon relative-MSEP approximation, with the
earlier influence supplied explicitly as `qPast`. -/
def rohrHorizonRelMsepApprox (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ) : ℝ :=
  ∑ j ∈ s, rohrHorizonTerm (uSq j) (qNow j) (qPast j)

/-- The sum of the process terms in the slide-17 horizon split. -/
def rohrHorizonProcessRelApprox (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ) : ℝ :=
  ∑ j ∈ s, rohrHorizonProcessTerm (uSq j) (qNow j) (qPast j)

/-- The sum of the parameter terms in the slide-17 horizon split. -/
def rohrHorizonParameterRelApprox (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ) : ℝ :=
  ∑ j ∈ s, rohrHorizonParameterTerm (uSq j) (qNow j) (qPast j)

/-- The `k`-year specialization of the slide-13 formula. The source index
`j-k` is evaluated when `k ≤ j` and extended by zero when `j < k`, as on the
slide. -/
def rohrKYearRelMsepApprox (s : Finset ℕ) (uSq q : ℕ → ℝ) (k : ℕ) : ℝ :=
  rohrHorizonRelMsepApprox s uSq q (fun j => if k ≤ j then q (j - k) else 0)

/-- The one-year specialization, with earlier influence `q̂_{j-1}` when
`1 ≤ j` and zero otherwise. -/
def rohrOneYearRelMsepApprox (s : Finset ℕ) (uSq q : ℕ → ℝ) : ℝ :=
  rohrHorizonRelMsepApprox s uSq q (fun j => if 1 ≤ j then q (j - 1) else 0)

/-! ## Exact process/parameter splits -/

/-- The ultimate-horizon split `u²q = u²(1-q)q + u²q²` from the first
line of slide 17. -/
theorem rohrUltimateTerm_split (uSq q : ℝ) :
    uSq * q = uSq * ((1 - q) * q) + uSq * q ^ 2 := by
  ring

/-- The ultimate relative approximation is its slide-17 process term plus its
parameter term. -/
theorem rohrUltimateRelMsepApprox_split (s : Finset ℕ) (uSq q : ℕ → ℝ) :
    rohrUltimateRelMsepApprox s uSq q
      = rohrUltimateProcessRelApprox s uSq q + rohrUltimateParameterRelApprox s uSq q := by
  unfold rohrUltimateRelMsepApprox rohrUltimateProcessRelApprox
    rohrUltimateParameterRelApprox
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => rohrUltimateTerm_split (uSq j) (q j)

/-- The exact rational identity behind the arbitrary-horizon split on slide
17. The earlier influence must differ from one because it is the denominator. -/
theorem rohrHorizonWeight_split (qNow qPast : ℝ) (hPast : qPast ≠ 1) :
    rohrHorizonWeight qNow qPast
      = (1 - qNow) * (qNow - qPast) / (1 - qPast) ^ 2
        + ((qNow - qPast) / (1 - qPast)) ^ 2 := by
  have hden : 1 - qPast ≠ 0 := sub_ne_zero.mpr hPast.symm
  unfold rohrHorizonWeight
  field_simp [hden]
  ring

/-- One arbitrary-horizon summand is exactly its process part plus its
parameter part. -/
theorem rohrHorizonTerm_split (uSq qNow qPast : ℝ) (hPast : qPast ≠ 1) :
    rohrHorizonTerm uSq qNow qPast
      = rohrHorizonProcessTerm uSq qNow qPast
        + rohrHorizonParameterTerm uSq qNow qPast := by
  rw [rohrHorizonTerm, rohrHorizonWeight_split qNow qPast hPast]
  unfold rohrHorizonProcessTerm rohrHorizonParameterTerm
  ring

/-- Röhr's arbitrary-horizon relative approximation is exactly the sum of
the process and parameter expressions displayed on slide 17. -/
theorem rohrHorizonRelMsepApprox_split (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ)
    (hPast : ∀ j ∈ s, qPast j ≠ 1) :
    rohrHorizonRelMsepApprox s uSq qNow qPast
      = rohrHorizonProcessRelApprox s uSq qNow qPast
        + rohrHorizonParameterRelApprox s uSq qNow qPast := by
  unfold rohrHorizonRelMsepApprox rohrHorizonProcessRelApprox
    rohrHorizonParameterRelApprox
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j hj =>
    rohrHorizonTerm_split (uSq j) (qNow j) (qPast j) (hPast j hj)

/-- The slide-17 split specialized directly to the `k`-year index `j-k`. -/
theorem rohrKYearRelMsepApprox_split (s : Finset ℕ) (uSq q : ℕ → ℝ) (k : ℕ)
    (hPast : ∀ j ∈ s, k ≤ j → q (j - k) ≠ 1) :
    rohrKYearRelMsepApprox s uSq q k
      = rohrHorizonProcessRelApprox s uSq q
          (fun j => if k ≤ j then q (j - k) else 0)
        + rohrHorizonParameterRelApprox s uSq q
          (fun j => if k ≤ j then q (j - k) else 0) := by
  apply rohrHorizonRelMsepApprox_split
  intro j hj
  split_ifs with hkj
  · exact hPast j hj hkj
  · norm_num

/-! ## Horizon endpoints and specializations -/

/-- With zero earlier influence, the horizon weight reduces to the current
influence. -/
theorem rohrHorizonWeight_zero_past (qNow : ℝ) :
    rohrHorizonWeight qNow 0 = qNow := by
  simp [rohrHorizonWeight]

/-- The zero-earlier-influence specialization of the horizon formula is the
ultimate-horizon formula. -/
theorem rohrHorizonRelMsepApprox_zero_past (s : Finset ℕ) (uSq q : ℕ → ℝ) :
    rohrHorizonRelMsepApprox s uSq q (fun _ => 0)
      = rohrUltimateRelMsepApprox s uSq q := by
  simp [rohrHorizonRelMsepApprox, rohrHorizonTerm, rohrHorizonWeight,
    rohrUltimateRelMsepApprox]

/-- The process summands reduce to the ultimate process summands when the
earlier influence is zero. -/
theorem rohrHorizonProcessRelApprox_zero_past (s : Finset ℕ) (uSq q : ℕ → ℝ) :
    rohrHorizonProcessRelApprox s uSq q (fun _ => 0)
      = rohrUltimateProcessRelApprox s uSq q := by
  simp [rohrHorizonProcessRelApprox, rohrHorizonProcessTerm,
    rohrUltimateProcessRelApprox]

/-- The parameter summands reduce to the ultimate parameter summands when the
earlier influence is zero. -/
theorem rohrHorizonParameterRelApprox_zero_past (s : Finset ℕ) (uSq q : ℕ → ℝ) :
    rohrHorizonParameterRelApprox s uSq q (fun _ => 0)
      = rohrUltimateParameterRelApprox s uSq q := by
  simp [rohrHorizonParameterRelApprox, rohrHorizonParameterTerm,
    rohrUltimateParameterRelApprox]

/-- Setting `k = 1` gives the one-year formula shown on slide 20. -/
theorem rohrKYearRelMsepApprox_one (s : Finset ℕ) (uSq q : ℕ → ℝ) :
    rohrKYearRelMsepApprox s uSq q 1 = rohrOneYearRelMsepApprox s uSq q := rfl

/-- The algebraic zero-year endpoint is zero when the source denominators are
defined: no influence has changed. -/
theorem rohrKYearRelMsepApprox_zero (s : Finset ℕ) (uSq q : ℕ → ℝ)
    (hPast : ∀ j ∈ s, q j ≠ 1) :
    rohrKYearRelMsepApprox s uSq q 0 = 0 := by
  unfold rohrKYearRelMsepApprox rohrHorizonRelMsepApprox
  apply sum_eq_zero
  intro j hj
  have hweight : rohrHorizonWeight (q j) (q j) = 0 := by
    simpa using rohrHorizonWeight_split (q j) (q j) (hPast j hj)
  simp [rohrHorizonTerm, hweight]

/-- If `k` reaches far enough back that every earlier influence in the sum is
zero, the `k`-year formula reduces to the ultimate formula. This is the source
convention `q̂ = 0` below the active index range stated as an explicit hypothesis. -/
theorem rohrKYearRelMsepApprox_eq_ultimate (s : Finset ℕ) (uSq q : ℕ → ℝ) (k : ℕ)
    (hzero : ∀ j ∈ s, k ≤ j → q (j - k) = 0) :
    rohrKYearRelMsepApprox s uSq q k = rohrUltimateRelMsepApprox s uSq q := by
  unfold rohrKYearRelMsepApprox rohrHorizonRelMsepApprox rohrHorizonTerm
    rohrUltimateRelMsepApprox
  exact sum_congr rfl fun j hj => by
    by_cases hkj : k ≤ j
    · simp [rohrHorizonWeight, hkj, hzero j hj hkj]
    · simp [rohrHorizonWeight, hkj]

/-! ## Nonnegativity and bounds under explicit influence conditions -/

/-- A horizon weight is nonnegative when influence has not decreased and the
earlier influence is below one. -/
theorem rohrHorizonWeight_nonneg (qNow qPast : ℝ) (hPastNow : qPast ≤ qNow)
    (hPastOne : qPast < 1) :
    0 ≤ rohrHorizonWeight qNow qPast := by
  exact div_nonneg (sub_nonneg.mpr hPastNow) (sub_pos.mpr hPastOne).le

/-- A horizon weight is at most one when current influence is at most one and
earlier influence is below one. -/
theorem rohrHorizonWeight_le_one (qNow qPast : ℝ) (hNowOne : qNow ≤ 1)
    (hPastOne : qPast < 1) :
    rohrHorizonWeight qNow qPast ≤ 1 := by
  rw [rohrHorizonWeight, div_le_one (sub_pos.mpr hPastOne)]
  linarith

/-- With nonnegative earlier influence and current influence at most one, a
horizon weight is at most the current influence. -/
theorem rohrHorizonWeight_le_current (qNow qPast : ℝ) (hPast : 0 ≤ qPast)
    (hNowOne : qNow ≤ 1) (hPastOne : qPast < 1) :
    rohrHorizonWeight qNow qPast ≤ qNow := by
  rw [rohrHorizonWeight, div_le_iff₀ (sub_pos.mpr hPastOne)]
  nlinarith [mul_nonneg hPast (sub_nonneg.mpr hNowOne)]

/-- Under monotone `[0,1]` influence conditions, the horizon weight lies in
`[0,1]`. -/
theorem rohrHorizonWeight_mem_Icc (qNow qPast : ℝ) (hPastZero : 0 ≤ qPast)
    (hPastNow : qPast ≤ qNow) (hNowOne : qNow ≤ 1) (hPastOne : qPast < 1) :
    rohrHorizonWeight qNow qPast ∈ Set.Icc 0 1 :=
  ⟨rohrHorizonWeight_nonneg qNow qPast hPastNow hPastOne,
    (rohrHorizonWeight_le_current qNow qPast hPastZero hNowOne hPastOne).trans hNowOne⟩

/-- A horizon approximation summand is nonnegative for a nonnegative squared
uncertainty and a nonnegative horizon weight. -/
theorem rohrHorizonTerm_nonneg (uSq qNow qPast : ℝ) (hu : 0 ≤ uSq)
    (hPastNow : qPast ≤ qNow) (hPastOne : qPast < 1) :
    0 ≤ rohrHorizonTerm uSq qNow qPast :=
  mul_nonneg hu (rohrHorizonWeight_nonneg qNow qPast hPastNow hPastOne)

/-- The process part is nonnegative when squared uncertainty is nonnegative,
current influence is at most one, and influence has not decreased. -/
theorem rohrHorizonProcessTerm_nonneg (uSq qNow qPast : ℝ) (hu : 0 ≤ uSq)
    (hPastNow : qPast ≤ qNow) (hNowOne : qNow ≤ 1) :
    0 ≤ rohrHorizonProcessTerm uSq qNow qPast := by
  exact mul_nonneg hu (div_nonneg
    (mul_nonneg (sub_nonneg.mpr hNowOne) (sub_nonneg.mpr hPastNow)) (sq_nonneg _))

/-- The parameter part is nonnegative whenever squared uncertainty is
nonnegative. -/
theorem rohrHorizonParameterTerm_nonneg (uSq qNow qPast : ℝ) (hu : 0 ≤ uSq) :
    0 ≤ rohrHorizonParameterTerm uSq qNow qPast :=
  mul_nonneg hu (sq_nonneg _)

/-- The arbitrary-horizon relative approximation is nonnegative under
pointwise monotone influence conditions. -/
theorem rohrHorizonRelMsepApprox_nonneg (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ)
    (hu : ∀ j ∈ s, 0 ≤ uSq j) (hPastNow : ∀ j ∈ s, qPast j ≤ qNow j)
    (hPastOne : ∀ j ∈ s, qPast j < 1) :
    0 ≤ rohrHorizonRelMsepApprox s uSq qNow qPast := by
  unfold rohrHorizonRelMsepApprox
  exact sum_nonneg fun j hj =>
    rohrHorizonTerm_nonneg (uSq j) (qNow j) (qPast j)
      (hu j hj) (hPastNow j hj) (hPastOne j hj)

/-- The process part of the horizon approximation is nonnegative under the
same pointwise monotonicity and upper-bound conditions. -/
theorem rohrHorizonProcessRelApprox_nonneg (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ)
    (hu : ∀ j ∈ s, 0 ≤ uSq j) (hPastNow : ∀ j ∈ s, qPast j ≤ qNow j)
    (hNowOne : ∀ j ∈ s, qNow j ≤ 1) :
    0 ≤ rohrHorizonProcessRelApprox s uSq qNow qPast := by
  unfold rohrHorizonProcessRelApprox
  exact sum_nonneg fun j hj =>
    rohrHorizonProcessTerm_nonneg (uSq j) (qNow j) (qPast j)
      (hu j hj) (hPastNow j hj) (hNowOne j hj)

/-- The parameter part of the horizon approximation is nonnegative when each
input squared uncertainty is nonnegative. -/
theorem rohrHorizonParameterRelApprox_nonneg (s : Finset ℕ) (uSq qNow qPast : ℕ → ℝ)
    (hu : ∀ j ∈ s, 0 ≤ uSq j) :
    0 ≤ rohrHorizonParameterRelApprox s uSq qNow qPast := by
  unfold rohrHorizonParameterRelApprox
  exact sum_nonneg fun j hj =>
    rohrHorizonParameterTerm_nonneg (uSq j) (qNow j) (qPast j) (hu j hj)

/-- With nonnegative squared uncertainties and influences in the source's
range, the horizon approximation is at most the ultimate approximation. -/
theorem rohrHorizonRelMsepApprox_le_ultimate (s : Finset ℕ)
    (uSq qNow qPast : ℕ → ℝ) (hu : ∀ j ∈ s, 0 ≤ uSq j)
    (hPast : ∀ j ∈ s, 0 ≤ qPast j) (hNowOne : ∀ j ∈ s, qNow j ≤ 1)
    (hPastOne : ∀ j ∈ s, qPast j < 1) :
    rohrHorizonRelMsepApprox s uSq qNow qPast
      ≤ rohrUltimateRelMsepApprox s uSq qNow := by
  unfold rohrHorizonRelMsepApprox rohrUltimateRelMsepApprox rohrHorizonTerm
  exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
    (rohrHorizonWeight_le_current (qNow j) (qPast j)
      (hPast j hj) (hNowOne j hj) (hPastOne j hj)) (hu j hj)

end

end VerifiedReserving
