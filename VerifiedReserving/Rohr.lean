import VerifiedReserving.TotalReserve

/-!
# Röhr (2016): the error-propagation form of the chain-ladder prediction error

Röhr, *Chain ladder and error propagation*, ASTIN Bulletin 46 (2016) 293-330,
derives the chain-ladder prediction error from the error-propagation formula:
the chain-ladder ultimate `Ĉ_{i,n-1} = C_{i,d} ∏_{k=d}^{n-2} f̂_k` (with
`d = n-1-i`) is a product, so a first-order expansion in the development
factors turns the relative squared error of the product into the *sum* of the
relative squared errors of the factors. The paper's classical-case display is

`msep(R̂_i) / Ĉ_{i,n-1}² = ∑_k û_k²`,

where `û_k²` is the relative uncertainty attached to development step `k`, and
the error-propagation derivation splits `û_k²` into a process part and a
parameter part,

`û_k² = σ̂_k² / (f̂_k² Ĉ_{i,k}) + σ̂_k² / (f̂_k² S_k)`,

the first from the conditional variance `σ_k² C_{i,k}` of the step itself, the
second from the estimation variance `σ_k² / S_k` of `f̂_k`. Summing and
multiplying back by `Ĉ_{i,n-1}²` gives Röhr's process term
`Ĉ² ∑_k σ̂_k²/(f̂_k² Ĉ_{i,k})` and his parameter term
`Ĉ² ∑_k σ̂_k²/(f̂_k² S_k)`.

**Source note.** The full text of Röhr (2016) is behind a paywall and was not
available here. What is formalized below is the classical-case (ultimate
run-off, single accident year) displayed formula as stated in the paper's own
abstract - "in the classical case treated by Mack (1993) the mean squared
prediction error divided by the squared estimated ultimate loss can be written
as `∑_j û_j²`, where `û_j` measures the relative uncertainty around the `j`-th
development factor and the proportion of the estimated ultimate loss that it
affects", together with "a split into process error and parameter error" - with
the two parts in the form quoted above. The general claims-development-result
formulas of that paper, between two arbitrary future horizons, are not
formalized here; neither is the paper's own aggregation over accident years,
which could not be checked against the source (see `rohrMsepTotal`).

## What is proved

* `rohrMsep_eq_rohrProcess_add_rohrParameter`: the split into process and
  parameter error, by construction.
* `rohrParameter_eq_mackEstimation`: Röhr's parameter term is exactly Mack's
  estimation-error term `Ĉ² ∑_k σ̂_k²/(f̂_k² S_k)`.
* `rohrProcess_eq_mackProcess`: Röhr's process term is exactly Mack's process
  variance `procVar` with `f̂, σ̂²` plugged in, that is, the solution of the
  variance recursion `V_{m+1} = f̂² V_m + σ̂² Ĉ` run along the row. This is the
  substantive identity: the linearized relative form and the recursive form of
  the process variance agree, provided the development factors and the
  projected claims along the row are nonzero.
* `rohrMsep_eq_msep`: **catalogue row 3.** Röhr's linearized single-accident-year
  prediction error equals Mack's 1993 closed form exactly, with no side
  condition. There is no correction term: the difference is zero, unlike the
  Mack-versus-BBMW row of `Catalogue.lean`.
* `msep_eq_mackProcess_add_mackEstimation`: a corollary that was missing from
  the library, obtained by reading Mack's closed form through Röhr's split -
  `msep` is the plug-in process variance plus the estimation term.
* `bbmwEstimation_sub_rohrParameter`: Röhr's parameter term is the first-order
  part of the conditional-resampling term of Buchwalder, Bühlmann, Merz and
  Wüthrich (2006); the exact remainder is the one from `Catalogue.lean`. This
  is what "linearized" buys and costs.

Everything here is deterministic algebra on the triangle, as in
`Recursion.lean` and `Catalogue.lean`; the stochastic content sits in the
theorems those definitions abbreviate.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-! ## Röhr's relative uncertainties -/

/-- Röhr's relative **process** uncertainty of the development step `k → k+1`
for accident year `i`: `σ̂_k² / (f̂_k² Ĉ_{i,k})`. It is the conditional variance
`σ̂_k² Ĉ_{i,k}` of the step divided by the squared mean `(f̂_k Ĉ_{i,k})²`. -/
def rohrRelProcess (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  sigma2 C n k / (fhat C n k ^ 2 * Chat C n i k)

/-- Röhr's relative **parameter** uncertainty of the development factor `k`:
`σ̂_k² / (f̂_k² S_k)`, the estimation variance of `f̂_k` relative to `f̂_k²`. -/
def rohrRelParam (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  sigma2 C n k / (fhat C n k ^ 2 * S C n k)

/-- Röhr's `û_k²`: the total relative uncertainty attached to development
step `k` along the row of accident year `i`. -/
def rohrRelVar (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  rohrRelProcess C n i k + rohrRelParam C n k

/-- Röhr's process-error term, `Ĉ_{i,n-1}² ∑_k σ̂_k²/(f̂_k² Ĉ_{i,k})`. -/
def rohrProcess (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), rohrRelProcess C n i k

/-- Röhr's parameter-error term, `Ĉ_{i,n-1}² ∑_k σ̂_k²/(f̂_k² S_k)`. -/
def rohrParameter (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), rohrRelParam C n k

/-- **Röhr's linearized prediction error** of the reserve of accident year `i`:
`Ĉ_{i,n-1}² ∑_k û_k²`. -/
def rohrMsep (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ :=
  (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), rohrRelVar C n i k

/-! ## The split into process error and parameter error -/

/-- Röhr's split: the linearized prediction error is process error plus
parameter error. -/
theorem rohrMsep_eq_rohrProcess_add_rohrParameter (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    rohrMsep C n i = rohrProcess C n i + rohrParameter C n i := by
  unfold rohrMsep rohrProcess rohrParameter rohrRelVar
  rw [← mul_add, ← sum_add_distrib]

/-- Röhr's relative parameter uncertainty is the `a_k` of the variant
catalogue. -/
theorem rohrRelParam_eq_relVar (C : ℕ → ℕ → ℝ) (n k : ℕ) :
    rohrRelParam C n k = relVar C n k := by
  unfold rohrRelParam relVar
  rw [div_div]

/-- **Röhr's parameter term is Mack's estimation-error term.** -/
theorem rohrParameter_eq_mackEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    rohrParameter C n i = mackEstimation C n i := by
  rw [mackEstimation_eq_sum_relVar, rohrParameter]
  exact congrArg _ (sum_congr rfl fun k _ => rohrRelParam_eq_relVar C n k)

/-! ## The process term is Mack's process variance -/

/-- The projection factorises along the row: for `n-1-i ≤ k ≤ m`,
`Ĉ_{i,m} = Ĉ_{i,k} ∏_{l=k}^{m-1} f̂_l`. -/
theorem Chat_eq_Chat_mul_prod (C : ℕ → ℕ → ℝ) (n i k m : ℕ)
    (hk : n - 1 - i ≤ k) (hkm : k ≤ m) :
    Chat C n i m = Chat C n i k * ∏ l ∈ Ico k m, fhat C n l := by
  unfold Chat
  rw [mul_assoc, Finset.prod_Ico_consecutive _ hk hkm]

/-- **Röhr's process term equals Mack's process variance.** The relative,
linearized form `Ĉ_{i,n-1}² ∑_k σ̂_k²/(f̂_k² Ĉ_{i,k})` and the recursive form
`procVar` with `f̂, σ̂²` plugged in are the same number, whenever the
development factors and the projected claims along the row are nonzero. -/
theorem rohrProcess_eq_mackProcess (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0)
    (hC : ∀ k ∈ Ico (n - 1 - i) (n - 1), Chat C n i k ≠ 0) :
    rohrProcess C n i = mackProcess C n i i := by
  have hdi : n - 1 - i + i = n - 1 := Nat.sub_add_cancel hi
  have hsub : n - 1 - (n - 1 - i) = i := by omega
  rw [mackProcess, procVar_eq_sum, hdi, rohrProcess, mul_sum,
    Finset.sum_Ico_eq_sum_range, hsub]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < i := mem_range.mp hj
  have hmem : n - 1 - i + j ∈ Ico (n - 1 - i) (n - 1) :=
    mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩
  have hlt : n - 1 - i + j < n - 1 := by omega
  have hfk := hf _ hmem
  have hCk := hC _ hmem
  -- the projected claims at step `k`, written out
  have hChat : C i (n - 1 - i) * ∏ l ∈ Ico (n - 1 - i) (n - 1 - i + j), fhat C n l
      = Chat C n i (n - 1 - i + j) := rfl
  -- the ultimate, split at step `k`
  have hU : ultimate C n i
      = Chat C n i (n - 1 - i + j) *
          (fhat C n (n - 1 - i + j) * ∏ l ∈ Ico (n - 1 - i + j + 1) (n - 1), fhat C n l) := by
    rw [show ultimate C n i = Chat C n i (n - 1) from rfl,
      Chat_eq_Chat_mul_prod C n i (n - 1 - i + j) (n - 1) (Nat.le_add_right _ _) hlt.le,
      Finset.prod_eq_prod_Ico_succ_bot hlt]
  rw [rohrRelProcess, hChat, hU]
  field_simp

/-! ## Catalogue row 3: Röhr 1993-classical case = Mack 1993 -/

/-- **Röhr = Mack.** Röhr's linearized single-accident-year prediction error is
Mack's 1993 closed form, with no side condition: the two displays are equal
term by term, so this catalogue row has zero correction term (contrast
`bbmwEstimation_sub_mackEstimation`). The reason no nonvanishing hypothesis is
needed is that `σ̂_k²/(f̂_k² Ĉ_{i,k})` and `(σ̂_k²/f̂_k²)(1/Ĉ_{i,k})` are the same
term of the language, Lean's division-by-zero convention included. -/
theorem rohrMsep_eq_msep (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    rohrMsep C n i = msep C n i := by
  unfold rohrMsep msep rohrRelVar rohrRelProcess rohrRelParam
  refine congrArg _ (sum_congr rfl fun k _ => ?_)
  rw [mul_add, mul_one_div, mul_one_div, div_div, div_div]

/-- Röhr's headline relative display: `msep / Ĉ_{i,n-1}² = ∑_k û_k²`. -/
theorem msep_div_ultimate_sq (C : ℕ → ℕ → ℝ) (n i : ℕ) (hU : ultimate C n i ≠ 0) :
    msep C n i / (ultimate C n i) ^ 2 = ∑ k ∈ Ico (n - 1 - i) (n - 1), rohrRelVar C n i k := by
  rw [← rohrMsep_eq_msep, rohrMsep, mul_comm, mul_div_assoc,
    div_self (pow_ne_zero 2 hU), mul_one]

/-- **Mack's closed form is process variance plus estimation error.** Reading
Mack's 1993 formula through Röhr's split identifies its two halves with the two
plug-in estimators of `Msep.lean`: the process part is `procVar` with `f̂, σ̂²`
substituted, the estimation part is `mackEstimation`. -/
theorem msep_eq_mackProcess_add_mackEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0)
    (hC : ∀ k ∈ Ico (n - 1 - i) (n - 1), Chat C n i k ≠ 0) :
    msep C n i = mackProcess C n i i + mackEstimation C n i := by
  rw [← rohrMsep_eq_msep, rohrMsep_eq_rohrProcess_add_rohrParameter,
    rohrProcess_eq_mackProcess C n i hi hf hC, rohrParameter_eq_mackEstimation]

/-- Röhr's linearized error, in the split form, against the two Mack plug-ins. -/
theorem rohrMsep_eq_mackProcess_add_mackEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0)
    (hC : ∀ k ∈ Ico (n - 1 - i) (n - 1), Chat C n i k ≠ 0) :
    rohrMsep C n i = mackProcess C n i i + mackEstimation C n i := by
  rw [rohrMsep_eq_msep, msep_eq_mackProcess_add_mackEstimation C n i hi hf hC]

/-- **What the linearization costs.** Röhr's parameter term is the first-order
part of the conditional-resampling term; the exact difference is the
product-minus-sum remainder of `Catalogue.lean`. -/
theorem bbmwEstimation_sub_rohrParameter (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    bbmwEstimation C n i - rohrParameter C n i
      = (ultimate C n i) ^ 2 *
          (∏ k ∈ Ico (n - 1 - i) (n - 1), (1 + relVar C n k) - 1
            - ∑ k ∈ Ico (n - 1 - i) (n - 1), relVar C n k) := by
  rw [rohrParameter_eq_mackEstimation, bbmwEstimation_sub_mackEstimation]

/-- Röhr's parameter term is at most the conditional-resampling term when the
relative estimation variances are nonnegative. -/
theorem rohrParameter_le_bbmwEstimation (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (ha : ∀ k ∈ Ico (n - 1 - i) (n - 1), 0 ≤ relVar C n k) :
    rohrParameter C n i ≤ bbmwEstimation C n i := by
  rw [rohrParameter_eq_mackEstimation]
  exact mackEstimation_le_bbmwEstimation C n i ha

/-! ## The total reserve

Röhr's paper is written for a single accident year and for the claims
development result between two horizons; its aggregation over accident years
could not be checked against the source, so the aggregate below is defined as
Röhr's single-year terms carried into Mack's Corollary, with Mack's cross
terms, and is recorded as a definition. What is proved is that the aggregate so
defined is Mack's `msepTotal`. -/

/-- Röhr's single-year terms aggregated with Mack's Corollary cross terms.
A definition: the cross terms are Mack's, not read off Röhr. -/
def rohrMsepTotal (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, rohrMsep C n i + ∑ i ∈ range n, mackCross C n i

/-- The aggregate of Röhr's single-year terms with Mack's cross terms is
Mack's total-reserve estimator. -/
theorem rohrMsepTotal_eq_msepTotal (C : ℕ → ℕ → ℝ) (n : ℕ) :
    rohrMsepTotal C n = msepTotal C n := by
  unfold rohrMsepTotal msepTotal
  exact congrArg (· + _) (sum_congr rfl fun i _ => rohrMsep_eq_msep C n i)

end

end VerifiedReserving
