import VerifiedReserving.Ultimate

/-!
# The one-year claims development result

Solvency II asks for the uncertainty of the *one-year* run-off, not of the
run-off to ultimate: how much can the booked reserve move over the next
twelve months? Merz and Wüthrich (2008, "Modelling the claims development
result for solvency purposes", CAS E-Forum) call that move the claims
development result and separate two objects.

The **true** claims development result of accident year `i` over the step
from information `D_k` to information `D_{k+1}` is

`CDR_i(k) = E[C_{i,n-1} | D_k] - E[C_{i,n-1} | D_{k+1}]`,

a difference of conditional expectations of the same ultimate claim under
successive information. This file defines it (`RandomTriangle.trueCDR`) and
proves the two statements Merz and Wüthrich open with.

* `condExp_trueCDR_eq_zero`: `E[CDR_i(k) | D_k] = 0` almost surely. The
  reserve set at time `k` is unbiased for what will be held at time `k+1`
  plus what will be paid in between. This is the tower property and nothing
  else: it uses only that `D` is a filtration inside the ambient σ-algebra,
  and holds for every accident year and every step.
* `trueCDR_eq`: under (M1) in the `D_k` form, the true CDR is a multiple of
  the one-step residual,
  `CDR_i(k) = (∏_{j ∈ [k+1, n-1)} f_j) (f_k C_{i,k} - C_{i,k+1})` a.e.
  Everything the next year of experience can do to the ultimate is carried
  by the single deviation of `C_{i,k+1}` from its prediction `f_k C_{i,k}`.

The filtration is the one carried by `RandomTriangle`: `D k` is everything
observed up to development year `k`, for all accident years. That is the
filtration in which Mack's (M1) is stated here, and the one the theorems of
`Stochastic.lean` and `Ultimate.lean` use. Merz and Wüthrich index
information by calendar year instead (`D_I = {C_{i,j} : i + j ≤ I}`, the
triangle after `I` diagonals). The martingale statement is the same tower
property in either filtration; the closed form is stated for the filtration
this library assumes (M1) in.

The **observable** claims development result is the difference of the two
chain-ladder predictions an actuary actually computes: the ultimate
estimated from the triangle with `n` diagonals, and the ultimate estimated a
year later from the triangle with `n+1` diagonals, with the development
factors re-estimated on the larger triangle. That is `obsCDR`, a definition
on a deterministic triangle, together with `RandomTriangle.obsCDRRv`, its
value along a random triangle. Only one fact is proved about it, an algebraic
one (`obsCDR_eq_reserve_sub`): it agrees with the form Merz and Wüthrich
display, opening reserve minus (payments of the year plus closing reserve).

Nothing is proved here about the distribution of the observable CDR. Merz
and Wüthrich's Results 3.1-3.3 (conditional mean squared error of prediction
of the observable CDR, and the estimator that goes into a Solvency II
one-year reserve risk figure) rest on an approximation step of the same
kind as Mack's: the estimated factors are treated as if the resampled ones,
and terms of second order in the residuals are dropped. That step is not
formalized, so no expectation, variance or MSEP statement about `obsCDR`
appears in this file. The boundary is deliberate: the true CDR results below
are exact, the observable-CDR results of the paper are not yet available
here.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-! ## The true claims development result -/

/-- The **true one-year claims development result** of accident year `i` over
the step from development year `k` to `k+1`:
`CDR_i(k) = E[C_{i,n-1} | D_k] - E[C_{i,n-1} | D_{k+1}]`, the change in the
predicted ultimate claim when the information grows by one year. -/
def RandomTriangle.trueCDR (X : RandomTriangle Ω n) (μ : Measure Ω) (i k : ℕ) : Ω → ℝ :=
  μ[X.C i (n - 1) | X.D k] - μ[X.C i (n - 1) | X.D (k + 1)]

theorem RandomTriangle.trueCDR_apply (X : RandomTriangle Ω n) (i k : ℕ) (ω : Ω) :
    X.trueCDR μ i k ω
      = (μ[X.C i (n - 1) | X.D k]) ω - (μ[X.C i (n - 1) | X.D (k + 1)]) ω := rfl

/-- **Merz-Wüthrich (2008): the true claims development result has conditional
mean zero.** `E[CDR_i(k) | D_k] = 0` almost surely: the ultimate predicted
with today's information is exactly what one expects to predict with next
year's information. The proof is the tower property through `D_{k+1} ⊇ D_k`;
the only hypotheses are the ones `condExp_condExp_of_le` asks for, namely
that `D` is a filtration inside the ambient σ-algebra (fields `D_mono`,
`D_le` of `RandomTriangle`) and that `μ` is finite, so the trimmed measures
are σ-finite. No integrability of `C_{i,n-1}` is needed for the identity as
stated: mathlib's conditional expectation is `0` off the integrable case, so
both terms vanish there; the statement carries its intended meaning exactly
when `C_{i,n-1}` is integrable. -/
theorem condExp_trueCDR_eq_zero [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (i k : ℕ) :
    μ[X.trueCDR μ i k | X.D k] =ᵐ[μ] 0 := by
  have hsub : μ[X.trueCDR μ i k | X.D k]
      =ᵐ[μ] μ[μ[X.C i (n - 1) | X.D k] | X.D k]
        - μ[μ[X.C i (n - 1) | X.D (k + 1)] | X.D k] :=
    condExp_sub integrable_condExp integrable_condExp _
  have h1 : μ[μ[X.C i (n - 1) | X.D k] | X.D k] =ᵐ[μ] μ[X.C i (n - 1) | X.D k] :=
    condExp_condExp_of_le le_rfl (X.D_le k)
  have h2 : μ[μ[X.C i (n - 1) | X.D (k + 1)] | X.D k] =ᵐ[μ] μ[X.C i (n - 1) | X.D k] :=
    condExp_condExp_of_le (X.D_mono (Nat.le_succ k)) (X.D_le (k + 1))
  filter_upwards [hsub, h1, h2] with ω hsubω h1ω h2ω
  rw [hsubω, Pi.sub_apply, h1ω, h2ω, sub_self, Pi.zero_apply]

/-- Iterating (M1) from an arbitrary development year `d`:
`E[C_{i,d+m} | D_d] = C_{i,d} ∏_{k ∈ [d, d+m)} f_k`. This is
`condExp_C_of_Mack1` with the starting year `d` free rather than pinned to
the latest observed year `n-1-i` of the row; the CDR needs it at `d = k` and
`d = k+1`. -/
theorem condExp_C_of_Mack1_at [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ)
    (i d m : ℕ) (hi : i < n) (hM : Mack1 X μ f) (hint : ∀ j, Integrable (X.C i j) μ) :
    μ[X.C i (d + m) | X.D d] =ᵐ[μ] fun ω => X.C i d ω * ∏ k ∈ Ico d (d + m), f k := by
  induction m with
  | zero =>
    have hmeas : StronglyMeasurable[X.D d] (X.C i d) := X.meas i d d le_rfl
    refine (condExp_of_stronglyMeasurable (X.D_le _) hmeas (hint _)).symm ▸ ?_
    exact Eventually.of_forall fun ω => by simp
  | succ m ih =>
    have h := condExp_C_succ X f i d (d + m) hi (Nat.le_add_right _ _) hM
    rw [show d + (m + 1) = d + m + 1 from rfl]
    refine h.trans ?_
    filter_upwards [ih] with ω hω
    rw [hω, prod_Ico_succ_top (Nat.le_add_right _ _)]
    ring

/-- The predicted ultimate under (M1) at any development year `k ≤ n-1`:
`E[C_{i,n-1} | D_k] = C_{i,k} ∏_{j ∈ [k, n-1)} f_j`. -/
theorem condExp_C_ultimate_of_Mack1 [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ)
    (i k : ℕ) (hi : i < n) (hk : k ≤ n - 1) (hM : Mack1 X μ f)
    (hint : ∀ j, Integrable (X.C i j) μ) :
    μ[X.C i (n - 1) | X.D k] =ᵐ[μ] fun ω => X.C i k ω * ∏ j ∈ Ico k (n - 1), f j := by
  have h := condExp_C_of_Mack1_at X f i k (n - 1 - k) hi hM hint
  rwa [show k + (n - 1 - k) = n - 1 from by omega] at h

/-- **Merz-Wüthrich (2008): the true CDR in terms of the one-step residual.**
Under (M1), for `k < n-1`,
`CDR_i(k) = (∏_{j ∈ [k+1, n-1)} f_j) (f_k C_{i,k} - C_{i,k+1})` almost surely.
The two predicted ultimates are `C_{i,k} ∏_{j ∈ [k, n-1)} f_j` and
`C_{i,k+1} ∏_{j ∈ [k+1, n-1)} f_j`; splitting the first product at its bottom
index leaves the common factor `∏_{j > k} f_j` times the deviation of the new
observation from its (M1) prediction. -/
theorem trueCDR_eq [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i k : ℕ)
    (hi : i < n) (hk : k < n - 1) (hM : Mack1 X μ f) (hint : ∀ j, Integrable (X.C i j) μ) :
    X.trueCDR μ i k
      =ᵐ[μ] fun ω =>
        (∏ j ∈ Ico (k + 1) (n - 1), f j) * (f k * X.C i k ω - X.C i (k + 1) ω) := by
  have h1 := condExp_C_ultimate_of_Mack1 X f i k hi hk.le hM hint
  have h2 := condExp_C_ultimate_of_Mack1 X f i (k + 1) hi hk hM hint
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [X.trueCDR_apply, hω1, hω2, Finset.prod_eq_prod_Ico_succ_bot hk f]
  ring

/-! ## The observable claims development result

Definitions only. The triangle with `n` diagonals is `C` read with the
parameter `n`: accident year `i` is observed up to development year `n-1-i`,
and `fhat C n k` averages over the rows `i ≤ n-k-2` that have both `C_{i,k}`
and `C_{i,k+1}`. One calendar year later the same data function is read with
the parameter `n+1`: every row has one more entry, the new diagonal
`i + j = n` is available, and `fhat C (n+1) k` re-estimates every development
factor on the enlarged triangle. -/

/-- The **observable one-year claims development result** of accident year `i`
over the calendar year that adds the `(n+1)`-st diagonal: the chain-ladder
ultimate computed from the triangle with `n` diagonals minus the chain-ladder
ultimate computed a year later, with all development factors re-estimated,
from the triangle with `n+1` diagonals.

Nothing is proved about its distribution. Merz and Wüthrich's mean squared
error of prediction for this quantity uses an approximation step (estimated
factors treated as resampled, second-order residual terms dropped) that is
not formalized in this library. -/
def obsCDR (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℝ := ultimate C n i - ultimate C (n + 1) i

/-- The observable CDR as Merz and Wüthrich display it: the reserve held at
the start of the year, minus the payments of the year and the reserve held at
the end of it. Pure algebra on the definitions; no probability, no
distributional claim. -/
theorem obsCDR_eq_reserve_sub (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    obsCDR C n i
      = reserve C n i - ((C i (n - i) - C i (n - 1 - i)) + reserve C (n + 1) i) := by
  simp only [obsCDR, reserve, Nat.add_sub_cancel]
  ring

/-- The observable CDR along a random triangle, outcome by outcome. -/
def RandomTriangle.obsCDRRv (X : RandomTriangle Ω n) (i : ℕ) : Ω → ℝ :=
  fun ω => obsCDR (X.at ω) n i

theorem RandomTriangle.obsCDRRv_apply (X : RandomTriangle Ω n) (i : ℕ) (ω : Ω) :
    X.obsCDRRv i ω = ultimate (X.at ω) n i - ultimate (X.at ω) (n + 1) i := rfl

end

end VerifiedReserving
