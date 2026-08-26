import VerifiedReserving.TotalReserve

/-!
# R ChainLadder `mse.method` semantics

This file transcribes the parameter-risk branch in R package `ChainLadder`
version 0.2.22, source commit
`41f4e949e5c3bffd7a18af2c0eaa98d6bae2da2f`.  The relevant source is
`R/MackChainLadderFunctions.R`, lines 229--299 at that commit.

The package stores standard errors and squares them inside the recursions.  We
store the squared parameter risk directly.  If `p` is the previous squared
parameter risk, `c` the projected cumulative claim (or the source's total
projected amount `M[k]`), `f` the development factor and `v = f.se[k]^2`, the
source step is

* `mse.method = "Mack"`: `c^2 v + p f^2`;
* `mse.method = "Independence"`: `c^2 v + p f^2 + p v`.

Thus the only option-dependent expression is the cross-product `p v`.  For one
accident year, the two recursions are proved below to give the existing Mack
sum (`mackEstimation`) and Murphy/BBMW product (`bbmwEstimation`) respectively.
For the total, the package runs the same step with `c = M[k]`; that generic
recursion and the two existing aggregate formula selectors are recorded
separately.  This is a formula-level transcription of the pinned source, not a
claim that Lean executed or verified the R runtime.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- The two accepted values of `MackChainLadder(..., mse.method=...)` in R
`ChainLadder` 0.2.22. -/
inductive ChainLadderMseMethod where
  | mack
  | independence
  deriving DecidableEq, Repr

/-- The option-dependent third term in the R parameter-risk recursion.  The
arguments are the previous squared parameter risk and `f.se[k]^2`. -/
def chainLadderParameterCross (method : ChainLadderMseMethod)
    (priorRiskSq factorVariance : ℝ) : ℝ :=
  match method with
  | .mack => 0
  | .independence => priorRiskSq * factorVariance

/-- One squared parameter-risk step from `MackRecursive.S.E` and
`TotalMack.S.E` in R `ChainLadder` 0.2.22.  The first argument after the method
is either the row projection or the source's total projected amount `M[k]`. -/
def chainLadderParameterStep (method : ChainLadderMseMethod)
    (projected factor factorVariance priorRiskSq : ℝ) : ℝ :=
  projected ^ 2 * factorVariance + priorRiskSq * factor ^ 2
    + chainLadderParameterCross method priorRiskSq factorVariance

@[simp] theorem chainLadderParameterCross_mack (p v : ℝ) :
    chainLadderParameterCross .mack p v = 0 := rfl

@[simp] theorem chainLadderParameterCross_independence (p v : ℝ) :
    chainLadderParameterCross .independence p v = p * v := rfl

/-- The source's `"Mack"` branch has no third term. -/
@[simp] theorem chainLadderParameterStep_mack (c f v p : ℝ) :
    chainLadderParameterStep .mack c f v p = c ^ 2 * v + p * f ^ 2 := by
  simp [chainLadderParameterStep]

/-- The source's `"Independence"` branch adds exactly `p * v`. -/
@[simp] theorem chainLadderParameterStep_independence (c f v p : ℝ) :
    chainLadderParameterStep .independence c f v p
      = c ^ 2 * v + p * f ^ 2 + p * v := by
  simp [chainLadderParameterStep]

/-- Exact difference between the two R source branches at one parameter-risk
step. -/
theorem chainLadderParameterStep_independence_sub_mack (c f v p : ℝ) :
    chainLadderParameterStep .independence c f v p
        - chainLadderParameterStep .mack c f v p = p * v := by
  simp [chainLadderParameterStep]

/-- Multiplier applied to the previous squared parameter risk. -/
def chainLadderParameterMultiplier (method : ChainLadderMseMethod)
    (factor factorVariance : ℝ) : ℝ :=
  match method with
  | .mack => factor ^ 2
  | .independence => factor ^ 2 + factorVariance

/-- Both source branches are one affine recurrence with a method-dependent
multiplier. -/
theorem chainLadderParameterStep_eq (method : ChainLadderMseMethod)
    (c f v p : ℝ) :
    chainLadderParameterStep method c f v p
      = c ^ 2 * v + p * chainLadderParameterMultiplier method f v := by
  cases method
  · simp [chainLadderParameterStep, chainLadderParameterMultiplier]
  · simp [chainLadderParameterStep, chainLadderParameterMultiplier]
    ring

/-- The per-accident-year squared parameter-risk recursion transcribed from
`MackRecursive.S.E`.  The package's squared `f.se[k]` is
`sigma2 C n k / S C n k` in the unit-weight, alpha-one model. -/
def chainLadderRowParameterRiskSq (method : ChainLadderMseMethod)
    (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      let k := n - 1 - i + m
      chainLadderParameterStep method (Chat C n i k) (fhat C n k)
        (sigma2 C n k / S C n k) (chainLadderRowParameterRiskSq method C n i m)

@[simp] theorem chainLadderRowParameterRiskSq_zero
    (method : ChainLadderMseMethod) (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    chainLadderRowParameterRiskSq method C n i 0 = 0 := rfl

theorem chainLadderRowParameterRiskSq_succ
    (method : ChainLadderMseMethod) (C : ℕ → ℕ → ℝ) (n i m : ℕ) :
    chainLadderRowParameterRiskSq method C n i (m + 1)
      = chainLadderParameterStep method (Chat C n i (n - 1 - i + m))
          (fhat C n (n - 1 - i + m))
          (sigma2 C n (n - 1 - i + m) / S C n (n - 1 - i + m))
          (chainLadderRowParameterRiskSq method C n i m) := rfl

/-- The package's squared factor standard error is `fhat^2 * relVar` whenever
the fitted development factor is nonzero.  No nonvanishing condition on `S` is
needed because both sides use Lean's totalized division. -/
theorem factorVariance_eq_factor_sq_mul_relVar
    (C : ℕ → ℕ → ℝ) (n k : ℕ) (hf : fhat C n k ≠ 0) :
    sigma2 C n k / S C n k = fhat C n k ^ 2 * relVar C n k := by
  unfold relVar
  rw [← mul_div_assoc]
  field_simp [hf]

/-- The per-row `"Mack"` recursion is the truncated sum of relative factor
variances. -/
theorem chainLadderRowParameterRiskSq_mack_eq_closed
    (C : ℕ → ℕ → ℝ) (n i m : ℕ)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhat C n k ≠ 0) :
    chainLadderRowParameterRiskSq .mack C n i m
      = Chat C n i (n - 1 - i + m) ^ 2
          * ∑ k ∈ Ico (n - 1 - i) (n - 1 - i + m), relVar C n k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hf' : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhat C n k ≠ 0 := by
      intro k hk
      exact hf k (Ico_subset_Ico_right (Nat.le_succ _) hk)
    have hfm : fhat C n (n - 1 - i + m) ≠ 0 :=
      hf _ (mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.lt_succ_self _⟩)
    rw [chainLadderRowParameterRiskSq_succ, chainLadderParameterStep_mack, ih hf',
      show n - 1 - i + (m + 1) = n - 1 - i + m + 1 from rfl,
      sum_Ico_succ_top (Nat.le_add_right _ _),
      Chat_succ C n i _ (Nat.le_add_right _ _),
      factorVariance_eq_factor_sq_mul_relVar C n _ hfm]
    ring

/-- The per-row `"Independence"` recursion is the truncated Murphy/BBMW
product of relative factor variances. -/
theorem chainLadderRowParameterRiskSq_independence_eq_closed
    (C : ℕ → ℕ → ℝ) (n i m : ℕ)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhat C n k ≠ 0) :
    chainLadderRowParameterRiskSq .independence C n i m
      = Chat C n i (n - 1 - i + m) ^ 2
          * (∏ k ∈ Ico (n - 1 - i) (n - 1 - i + m), (1 + relVar C n k) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hf' : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhat C n k ≠ 0 := by
      intro k hk
      exact hf k (Ico_subset_Ico_right (Nat.le_succ _) hk)
    have hfm : fhat C n (n - 1 - i + m) ≠ 0 :=
      hf _ (mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.lt_succ_self _⟩)
    rw [chainLadderRowParameterRiskSq_succ, chainLadderParameterStep_independence,
      ih hf', show n - 1 - i + (m + 1) = n - 1 - i + m + 1 from rfl,
      prod_Ico_succ_top (Nat.le_add_right _ _),
      Chat_succ C n i _ (Nat.le_add_right _ _),
      factorVariance_eq_factor_sq_mul_relVar C n _ hfm]
    ring

/-- At the ultimate, the R `"Mack"` row recursion is exactly the existing
Mack estimation-error term. -/
theorem chainLadderRowParameterRiskSq_mack_eq_mackEstimation
    (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0) :
    chainLadderRowParameterRiskSq .mack C n i i = mackEstimation C n i := by
  have hd : n - 1 - i + i = n - 1 := Nat.sub_add_cancel hi
  rw [chainLadderRowParameterRiskSq_mack_eq_closed C n i i (by rwa [hd]), hd,
    mackEstimation_eq_sum_relVar]
  rfl

/-- At the ultimate, the R `"Independence"` row recursion is exactly the
existing Murphy/BBMW conditional-resampling term. -/
theorem chainLadderRowParameterRiskSq_independence_eq_bbmwEstimation
    (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0) :
    chainLadderRowParameterRiskSq .independence C n i i = bbmwEstimation C n i := by
  have hd : n - 1 - i + i = n - 1 := Nat.sub_add_cancel hi
  rw [chainLadderRowParameterRiskSq_independence_eq_closed C n i i (by rwa [hd]), hd]
  rfl

/-- The total squared parameter-risk recursion transcribed from
`TotalMack.S.E`.  Here `M k` is the source's sum of projected claims at
development period `k`, and `factorVariance k` is `f.se[k]^2`. -/
def chainLadderTotalParameterRiskSq (method : ChainLadderMseMethod)
    (M factor factorVariance : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => chainLadderParameterStep method (M k) (factor k)
      (factorVariance k) (chainLadderTotalParameterRiskSq method M factor factorVariance k)

@[simp] theorem chainLadderTotalParameterRiskSq_zero
    (method : ChainLadderMseMethod) (M factor factorVariance : ℕ → ℝ) :
    chainLadderTotalParameterRiskSq method M factor factorVariance 0 = 0 := rfl

/-- The total `"Mack"` recursion omits the cross-product term. -/
theorem chainLadderTotalParameterRiskSq_mack_succ
    (M factor factorVariance : ℕ → ℝ) (k : ℕ) :
    chainLadderTotalParameterRiskSq .mack M factor factorVariance (k + 1)
      = M k ^ 2 * factorVariance k
        + chainLadderTotalParameterRiskSq .mack M factor factorVariance k * factor k ^ 2 := by
  simp [chainLadderTotalParameterRiskSq]

/-- The total `"Independence"` recursion adds the previous squared parameter
risk times `f.se[k]^2`, exactly as the per-row recursion does. -/
theorem chainLadderTotalParameterRiskSq_independence_succ
    (M factor factorVariance : ℕ → ℝ) (k : ℕ) :
    chainLadderTotalParameterRiskSq .independence M factor factorVariance (k + 1)
      = M k ^ 2 * factorVariance k
        + chainLadderTotalParameterRiskSq .independence M factor factorVariance k * factor k ^ 2
        + chainLadderTotalParameterRiskSq .independence M factor factorVariance k
            * factorVariance k := by
  simp [chainLadderTotalParameterRiskSq]

/-- Closed form of the total source recursion for either option.  The Mack
branch propagates each increment by later `f^2`; the Independence branch by
later `f^2 + f.se^2`. -/
theorem chainLadderTotalParameterRiskSq_eq_sum
    (method : ChainLadderMseMethod) (M factor factorVariance : ℕ → ℝ) (m : ℕ) :
    chainLadderTotalParameterRiskSq method M factor factorVariance m
      = ∑ k ∈ range m, M k ^ 2 * factorVariance k
          * ∏ l ∈ Ico (k + 1) m,
              chainLadderParameterMultiplier method (factor l) (factorVariance l) := by
  induction m with
  | zero => simp [chainLadderTotalParameterRiskSq]
  | succ m ih =>
    rw [chainLadderTotalParameterRiskSq, chainLadderParameterStep_eq, ih, sum_range_succ,
      sum_mul]
    rw [add_comm]
    congr 1
    · refine sum_congr rfl fun k hk => ?_
      have hkm : k + 1 ≤ m := by
        have := mem_range.mp hk
        omega
      rw [prod_Ico_succ_top hkm]
      ring
    · simp

/-- Closed-form parameter term selected by the R option for one accident year.
The recurrence equivalence is proved above rather than assumed here. -/
def chainLadderRowParameterFormula (method : ChainLadderMseMethod)
    (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  match method with
  | .mack => mackEstimation C n i
  | .independence => bbmwEstimation C n i

/-- Aggregate parameter term selected by the package option: Mack's Corollary
or the Murphy/BBMW conditional-resampling counterpart already formalized in
`TotalReserve.lean`. -/
def chainLadderTotalParameterFormula (method : ChainLadderMseMethod)
    (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  match method with
  | .mack => mackTotalEstimation C n
  | .independence => bbmwTotalEstimation C n

@[simp] theorem chainLadderRowParameterFormula_mack
    (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    chainLadderRowParameterFormula .mack C n i = mackEstimation C n i := rfl

@[simp] theorem chainLadderRowParameterFormula_independence
    (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    chainLadderRowParameterFormula .independence C n i = bbmwEstimation C n i := rfl

@[simp] theorem chainLadderTotalParameterFormula_mack
    (C : ℕ → ℕ → ℝ) (n : ℕ) :
    chainLadderTotalParameterFormula .mack C n = mackTotalEstimation C n := rfl

@[simp] theorem chainLadderTotalParameterFormula_independence
    (C : ℕ → ℕ → ℝ) (n : ℕ) :
    chainLadderTotalParameterFormula .independence C n = bbmwTotalEstimation C n := rfl

/-- The exact aggregate difference selected by the two option values is the
existing row-wise BBMW-minus-Mack remainder. -/
theorem chainLadderTotalParameterFormula_independence_sub_mack
    (C : ℕ → ℕ → ℝ) (n : ℕ) :
    chainLadderTotalParameterFormula .independence C n
        - chainLadderTotalParameterFormula .mack C n
      = ∑ i ∈ range n,
          ((ultimate C n i) ^ 2 + 2 * ultimate C n i * laterUltimates C n i)
            * (rowProd C n i - rowSum C n i) := by
  exact bbmwTotalEstimation_sub_mackTotalEstimation C n

end

end VerifiedReserving
