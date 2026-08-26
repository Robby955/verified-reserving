import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Panjer recursion for compound distributions

Panjer, *Recursive Evaluation of a Family of Compound Distributions*,
ASTIN Bulletin 12 (1981), 22--26, considers claim-count masses satisfying

`pₙ = pₙ₋₁ (a + b / n)` for `n >= 1`.

For a severity mass `f` supported on the positive integers and compound
aggregate mass `g`, his equation (5) is

`g i = sum_{j=1}^i (a + b*j/i) * f j * g (i-j)` for `i >= 1`,
with `g 0 = p 0`.

This module represents probability generating functions as formal power
series. The count recurrence is first proved equivalent to its differential
equation. Formal substitution gives the compound generating function, and the
chain rule gives the coefficient recursion. The algebra does not require
nonnegativity or normalization; those conditions are needed only to interpret
the coefficients as probability masses.
-/

open Finset PowerSeries

namespace VerifiedReserving

noncomputable section

/-- Formal probability generating series with coefficient sequence `mass`. -/
def massSeries (mass : ℕ → ℝ) : ℝ⟦X⟧ := PowerSeries.mk mass

@[simp]
theorem coeff_massSeries (mass : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (massSeries mass) = mass n := by
  simp [massSeries]

/-- Panjer's `(a,b,0)` claim-count recurrence, written without division. -/
def PanjerFrequency (mass : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * mass (n + 1) =
    (a * ((n + 1 : ℕ) : ℝ) + b) * mass n

/-- The count recurrence is the coefficient form of
`P' = (a+b)P + a X P'`. -/
theorem panjerFrequency_iff_derivative (mass : ℕ → ℝ) (a b : ℝ) :
    PanjerFrequency mass a b ↔
      PowerSeries.derivative ℝ (massSeries mass) =
        (a + b) • massSeries mass +
          a • (PowerSeries.X * PowerSeries.derivative ℝ (massSeries mass)) := by
  constructor
  · intro h
    ext n
    rw [PowerSeries.coeff_derivative, coeff_massSeries]
    simp only [map_add, PowerSeries.coeff_smul, coeff_massSeries, smul_eq_mul]
    have hx : PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℝ (massSeries mass)) =
        (n : ℝ) * mass n := by
      cases n with
      | zero => simp
      | succ n =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
            coeff_massSeries]
          norm_num
          ring
    rw [hx]
    have hn := h n
    norm_num at hn ⊢
    linear_combination hn
  · intro h n
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_derivative, coeff_massSeries] at hn
    simp only [map_add, PowerSeries.coeff_smul, coeff_massSeries, smul_eq_mul] at hn
    have hx : PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative ℝ (massSeries mass)) =
        (n : ℝ) * mass n := by
      cases n with
      | zero => simp
      | succ n =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
            coeff_massSeries]
          norm_num
          ring
    rw [hx] at hn
    norm_num at hn ⊢
    linear_combination hn

/-- Formal generating series of the compound aggregate. Substitution is
well behaved when the severity series has zero constant coefficient. -/
def compoundMassSeries (frequency severity : ℕ → ℝ) : ℝ⟦X⟧ :=
  (massSeries frequency).subst (massSeries severity)

/-- Coefficients of the compound generating series. -/
def compoundMass (frequency severity : ℕ → ℝ) (i : ℕ) : ℝ :=
  PowerSeries.coeff i (compoundMassSeries frequency severity)

@[simp]
theorem coeff_compoundMassSeries (frequency severity : ℕ → ℝ) (i : ℕ) :
    PowerSeries.coeff i (compoundMassSeries frequency severity) =
      compoundMass frequency severity i := rfl

/-- A positive-integer severity series has zero constant coefficient and can
therefore be substituted into an arbitrary formal power series. -/
theorem hasSubst_massSeries {severity : ℕ → ℝ} (hzero : severity 0 = 0) :
    PowerSeries.HasSubst (massSeries severity) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_massSeries, hzero]

/-- The coefficient of the composed generating series is the usual compound
mixture of convolution powers, Panjer's equation (6). -/
theorem compoundMass_eq_finsum (frequency severity : ℕ → ℝ) (i : ℕ)
    (hzero : severity 0 = 0) :
    compoundMass frequency severity i =
      finsum (fun claimCount : ℕ =>
        frequency claimCount *
          PowerSeries.coeff i ((massSeries severity) ^ claimCount)) := by
  rw [compoundMass, compoundMassSeries,
    PowerSeries.coeff_subst' (hasSubst_massSeries hzero)]
  apply finsum_congr
  intro claimCount
  simp [smul_eq_mul]

/-- Differential equation for the compound generating series. This is the
formal-series chain rule applied to the Panjer frequency equation. -/
theorem derivative_compoundMassSeries
    (frequency severity : ℕ → ℝ) (a b : ℝ)
    (hfrequency : PanjerFrequency frequency a b)
    (hzero : severity 0 = 0) :
    PowerSeries.derivative ℝ (compoundMassSeries frequency severity) =
      (a + b) •
          (PowerSeries.derivative ℝ (massSeries severity) *
            compoundMassSeries frequency severity) +
        a • (massSeries severity *
          PowerSeries.derivative ℝ (compoundMassSeries frequency severity)) := by
  let P := massSeries frequency
  let F := massSeries severity
  have hF : PowerSeries.HasSubst F := hasSubst_massSeries hzero
  have hP : PowerSeries.derivative ℝ P =
      (a + b) • P + a • (PowerSeries.X * PowerSeries.derivative ℝ P) :=
    (panjerFrequency_iff_derivative frequency a b).1 hfrequency
  have hsub := congrArg (fun q : ℝ⟦X⟧ => q.subst F) hP
  simp only [PowerSeries.subst_add hF, PowerSeries.subst_smul hF,
    PowerSeries.subst_mul hF, PowerSeries.subst_X hF] at hsub
  change PowerSeries.derivative ℝ (P.subst F) =
    (a + b) • (PowerSeries.derivative ℝ F * P.subst F) +
      a • (F * PowerSeries.derivative ℝ (P.subst F))
  rw [PowerSeries.derivative_subst ℝ hF]
  nth_rewrite 1 [hsub]
  simp only [PowerSeries.smul_eq_C_mul]
  ring

/-- Panjer's equation (5), multiplied by its positive index. The antidiagonal
encodes `j + k = i`; the `j = 0` term vanishes for positive severities. -/
def panjerWeightedSum (a b : ℝ) (severity aggregate : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal i,
    (a * (i : ℝ) + b * (p.1 : ℝ)) * severity p.1 * aggregate p.2

/-- Coefficient form of the two derivative products in the compound
differential equation. -/
theorem panjerWeightedSum_succ_eq_coeff
    (a b : ℝ) (severity aggregate : ℕ → ℝ) (n : ℕ) :
    panjerWeightedSum a b severity aggregate (n + 1) =
      (a + b) * PowerSeries.coeff n
        (PowerSeries.derivative ℝ (massSeries severity) * massSeries aggregate) +
      a * PowerSeries.coeff n
        (massSeries severity * PowerSeries.derivative ℝ (massSeries aggregate)) := by
  unfold panjerWeightedSum
  have hsplit :
      (∑ p ∈ Finset.antidiagonal (n + 1),
          (a * ((n + 1 : ℕ) : ℝ) + b * (p.1 : ℝ)) *
            severity p.1 * aggregate p.2) =
        (a + b) * (∑ p ∈ Finset.antidiagonal (n + 1),
          (p.1 : ℝ) * severity p.1 * aggregate p.2) +
        a * (∑ p ∈ Finset.antidiagonal (n + 1),
          (p.2 : ℝ) * severity p.1 * aggregate p.2) := by
    rw [mul_sum, mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p hp => by
      have hpNat := Finset.mem_antidiagonal.mp hp
      have hpReal : (p.1 : ℝ) + (p.2 : ℝ) = ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hpNat
      rw [← hpReal]
      ring
  rw [hsplit, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  congr 1
  · congr 1
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, zero_mul, zero_add, coeff_massSeries,
      PowerSeries.coeff_derivative]
    exact Finset.sum_congr rfl fun p _ => by
      push_cast
      ring
  · congr 1
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.cast_zero, zero_mul, zero_add, coeff_massSeries,
      PowerSeries.coeff_derivative]
    exact Finset.sum_congr rfl fun p _ => by
      push_cast
      ring

/-- The compound coefficients satisfy Panjer's recursion after multiplying
the `i`th equation by `i`. -/
theorem compoundMass_panjerWeighted_succ
    (frequency severity : ℕ → ℝ) (a b : ℝ) (n : ℕ)
    (hfrequency : PanjerFrequency frequency a b)
    (hzero : severity 0 = 0) :
    (((n + 1 : ℕ) : ℝ) * compoundMass frequency severity (n + 1)) =
      panjerWeightedSum a b severity (compoundMass frequency severity) (n + 1) := by
  have hD := derivative_compoundMassSeries frequency severity a b hfrequency hzero
  have hc := congrArg (PowerSeries.coeff n) hD
  simp only [PowerSeries.coeff_derivative, coeff_compoundMassSeries, map_add,
    PowerSeries.coeff_smul, smul_eq_mul] at hc
  rw [panjerWeightedSum_succ_eq_coeff a b severity
    (compoundMass frequency severity) n]
  have hseries : massSeries (compoundMass frequency severity) =
      compoundMassSeries frequency severity := by
    ext i
    simp
  rw [hseries]
  rw [mul_comm]
  norm_num at hc ⊢
  exact hc

/-- The right side of Panjer's discrete recursion. The antidiagonal indexes
all `j + k = i`; when `severity 0 = 0`, the `j = 0` term is zero and the sum
is exactly the source's `j = 1, ..., i` sum. -/
def panjerRecursionSum (a b : ℝ) (severity aggregate : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal i,
    (a + b * (p.1 : ℝ) / (i : ℝ)) * severity p.1 * aggregate p.2

/-- The multiplied and divided forms of the recursion agree at every positive
index. -/
theorem panjerWeightedSum_eq_mul_recursionSum
    (a b : ℝ) (severity aggregate : ℕ → ℝ) (i : ℕ) (hi : i ≠ 0) :
    panjerWeightedSum a b severity aggregate i =
      (i : ℝ) * panjerRecursionSum a b severity aggregate i := by
  unfold panjerWeightedSum panjerRecursionSum
  rw [mul_sum]
  exact Finset.sum_congr rfl fun p _ => by
    have hiReal : (i : ℝ) ≠ 0 := by exact_mod_cast hi
    field_simp [hiReal]

/-- **Panjer (1981), equation (5).** For positive-integer severities, the
compound generating-function coefficients obey the discrete Panjer recursion
at every positive index. -/
theorem compoundMass_panjer_succ
    (frequency severity : ℕ → ℝ) (a b : ℝ) (n : ℕ)
    (hfrequency : PanjerFrequency frequency a b)
    (hzero : severity 0 = 0) :
    compoundMass frequency severity (n + 1) =
      panjerRecursionSum a b severity (compoundMass frequency severity) (n + 1) := by
  have hweighted := compoundMass_panjerWeighted_succ frequency severity a b n
    hfrequency hzero
  rw [panjerWeightedSum_eq_mul_recursionSum a b severity
    (compoundMass frequency severity) (n + 1) (by omega)] at hweighted
  have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  exact hweighted

/-- Panjer's initial condition `g 0 = p 0` for severities supported on the
positive integers. -/
theorem compoundMass_zero (frequency severity : ℕ → ℝ)
    (hzero : severity 0 = 0) :
    compoundMass frequency severity 0 = frequency 0 := by
  have hF := hasSubst_massSeries hzero
  have hconst : PowerSeries.constantCoeff (massSeries severity) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_massSeries, hzero]
  rw [compoundMass, compoundMassSeries, PowerSeries.coeff_subst' hF]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hconst, hd]

/-- Panjer's equation (5) in its printed index range, reindexed by
`r = j - 1`: `r` runs from `0` through `i-1`. -/
def panjerEquation5 (a b : ℝ) (severity aggregate : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ r ∈ Finset.range i,
    (a + b * ((r + 1 : ℕ) : ℝ) / (i : ℝ)) * severity (r + 1) *
      aggregate (i - (r + 1))

/-- The antidiagonal recurrence sum is exactly Panjer's printed
`j = 1, ..., i` sum when the severity mass at zero vanishes. -/
theorem panjerRecursionSum_succ_eq_equation5
    (a b : ℝ) (severity aggregate : ℕ → ℝ) (n : ℕ)
    (hzero : severity 0 = 0) :
    panjerRecursionSum a b severity aggregate (n + 1) =
      panjerEquation5 a b severity aggregate (n + 1) := by
  unfold panjerRecursionSum panjerEquation5
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp [hzero]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Panjer's equation (5) stated in the source's printed index range. -/
theorem compoundMass_panjer_equation5
    (frequency severity : ℕ → ℝ) (a b : ℝ) (n : ℕ)
    (hfrequency : PanjerFrequency frequency a b)
    (hzero : severity 0 = 0) :
    compoundMass frequency severity (n + 1) =
      panjerEquation5 a b severity (compoundMass frequency severity) (n + 1) := by
  rw [compoundMass_panjer_succ frequency severity a b n hfrequency hzero,
    panjerRecursionSum_succ_eq_equation5 a b severity
      (compoundMass frequency severity) n hzero]

/-! ## Source-family and unit-severity checks -/

/-- Geometric claim-count masses, one of the four examples in Panjer's
Section 2. Normalization and parameter-range conditions are separate from the
algebraic recurrence. -/
def geometricFrequencyMass (q : ℝ) (n : ℕ) : ℝ :=
  (1 - q) * q ^ n

theorem geometricFrequencyMass_panjer (q : ℝ) :
    PanjerFrequency (geometricFrequencyMass q) q 0 := by
  intro n
  simp only [geometricFrequencyMass, add_zero, pow_succ]
  push_cast
  ring

/-- Point mass at severity one. -/
def unitSeverityMass (j : ℕ) : ℝ := if j = 1 then 1 else 0

@[simp]
theorem unitSeverityMass_zero : unitSeverityMass 0 = 0 := by
  simp [unitSeverityMass]

theorem massSeries_unitSeverityMass : massSeries unitSeverityMass = PowerSeries.X := by
  ext j
  simp [unitSeverityMass, PowerSeries.coeff_X]

/-- Compounding with deterministic unit severities leaves the count mass
unchanged. This checks both the composition definition and every recursion
index against a nontrivial infinite count sequence. -/
theorem compoundMass_unitSeverity (frequency : ℕ → ℝ) (i : ℕ) :
    compoundMass frequency unitSeverityMass i = frequency i := by
  rw [compoundMass, compoundMassSeries, massSeries_unitSeverityMass,
    PowerSeries.X_subst, coeff_massSeries]

/-- The geometric/unit-severity instance satisfies the printed recursion. -/
theorem geometric_unitSeverity_panjer_equation5 (q : ℝ) (n : ℕ) :
    geometricFrequencyMass q (n + 1) =
      panjerEquation5 q 0 unitSeverityMass (geometricFrequencyMass q) (n + 1) := by
  rw [← compoundMass_unitSeverity (geometricFrequencyMass q) (n + 1),
    compoundMass_panjer_equation5 (geometricFrequencyMass q) unitSeverityMass q 0 n
      (geometricFrequencyMass_panjer q) unitSeverityMass_zero]
  congr 1
  funext i
  exact compoundMass_unitSeverity (geometricFrequencyMass q) i

end

end VerifiedReserving
