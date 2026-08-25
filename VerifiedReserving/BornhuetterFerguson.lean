import VerifiedReserving.ChainLadder

/-!
# Bornhuetter-Ferguson on the chain-ladder pattern

The Bornhuetter-Ferguson (BF) method replaces the chain-ladder ultimate by an
a priori ultimate `U` (typically premium times an expected loss ratio) and
applies the chain-ladder development pattern to it:

`R^BF_i = U (1 - 1 / ∏_{k=d}^{n-2} f̂_k)`,  `Ĉ^BF_{i,n-1} = C_{i,d} + R^BF_i`.

Deterministic facts proved here:

* the BF reserve is linear in the a priori ultimate;
* with `U` equal to the chain-ladder ultimate, BF returns the chain-ladder
  ultimate exactly (the well-known "BF is CL with a different prior");
* the percentage-reported factor `1 / ∏ f̂_k` lies in `[0, 1]` when every
  factor is at least `1`, so the BF reserve is a fraction of `U`.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- Cumulative development factor from the latest diagonal to ultimate,
`∏_{k=d}^{n-2} f̂_k` with `d = n-1-i`. -/
def cdf (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  ∏ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k

/-- Bornhuetter-Ferguson reserve with a priori ultimate `U`. -/
def bfReserve (C : ℕ → ℕ → ℝ) (n i : ℕ) (U : ℝ) : ℝ :=
  U * (1 - 1 / cdf C n i)

/-- Bornhuetter-Ferguson ultimate. -/
def bfUltimate (C : ℕ → ℕ → ℝ) (n i : ℕ) (U : ℝ) : ℝ :=
  C i (n - 1 - i) + bfReserve C n i U

theorem ultimate_eq_mul_cdf (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    ultimate C n i = C i (n - 1 - i) * cdf C n i := by
  rfl

/-- The BF reserve is linear in the a priori ultimate. -/
theorem bfReserve_smul (C : ℕ → ℕ → ℝ) (n i : ℕ) (a U : ℝ) :
    bfReserve C n i (a * U) = a * bfReserve C n i U := by
  unfold bfReserve; ring

theorem bfReserve_add (C : ℕ → ℕ → ℝ) (n i : ℕ) (U V : ℝ) :
    bfReserve C n i (U + V) = bfReserve C n i U + bfReserve C n i V := by
  unfold bfReserve; ring

/-- **BF with the chain-ladder prior is chain ladder.** If the a priori ultimate
is the chain-ladder ultimate and the cumulative factor is nonzero, the BF
ultimate equals the chain-ladder ultimate. -/
theorem bfUltimate_of_ultimate (C : ℕ → ℕ → ℝ) (n i : ℕ) (h : cdf C n i ≠ 0) :
    bfUltimate C n i (ultimate C n i) = ultimate C n i := by
  unfold bfUltimate bfReserve
  rw [ultimate_eq_mul_cdf]
  field_simp
  ring

/-- Correspondingly the BF reserve with the chain-ladder prior is the
chain-ladder reserve. -/
theorem bfReserve_of_ultimate (C : ℕ → ℕ → ℝ) (n i : ℕ) (h : cdf C n i ≠ 0) :
    bfReserve C n i (ultimate C n i) = reserve C n i := by
  have := bfUltimate_of_ultimate C n i h
  unfold bfUltimate at this
  unfold reserve
  linarith

/-- If every development factor along the row is at least `1`, the cumulative
factor is at least `1`. -/
theorem one_le_cdf (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), 1 ≤ fhat C n k) :
    1 ≤ cdf C n i := by
  unfold cdf
  exact Finset.one_le_prod hf

/-- Under the same hypothesis the percentage reported `1 / cdf` lies in `(0, 1]`,
so the BF reserve is a nonnegative fraction of a nonnegative prior. -/
theorem bfReserve_nonneg (C : ℕ → ℕ → ℝ) (n i : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), 1 ≤ fhat C n k) :
    0 ≤ bfReserve C n i U := by
  unfold bfReserve
  have h1 : 1 ≤ cdf C n i := one_le_cdf C n i hf
  have h2 : 1 / cdf C n i ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact h1
  exact mul_nonneg hU (by linarith)

theorem bfReserve_le (C : ℕ → ℕ → ℝ) (n i : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), 1 ≤ fhat C n k) :
    bfReserve C n i U ≤ U := by
  unfold bfReserve
  have h1 : 1 ≤ cdf C n i := one_le_cdf C n i hf
  have h2 : 0 ≤ 1 / cdf C n i := by positivity
  nlinarith

end

end VerifiedReserving
