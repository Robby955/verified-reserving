import VerifiedReserving.Recursion
import VerifiedReserving.Stochastic

/-!
# Mack (1999): general weights and exponent

Mack, *The standard error of chain ladder reserve estimates: recursive
calculation and inclusion of a tail factor*, ASTIN Bulletin 29 (1999) 361-366,
generalizes the 1993 development factor to

`f̂_k = (∑_i w_{ik} C_{ik}^α F_{ik}) / (∑_i w_{ik} C_{ik}^α)`,   `F_{ik} = C_{i,k+1}/C_{ik}`,

with weights `w_{ik} ∈ [0,1]` and an exponent `α`. The three cases the paper
names are `α = 1` with unit weights (the 1993 estimator), `α = 0` (the simple
average of the individual factors) and `α = 2` (the ordinary regression of
`C_{i,k+1}` on `C_{ik}` through the origin). The variance assumption becomes
`Var(F_{ik} | ⋯) = σ_k² / (w_{ik} C_{ik}^α)` and the variance estimator

`σ̂_k² = (n-k-2)⁻¹ ∑_i w_{ik} C_{ik}^α (F_{ik} - f̂_k)²`.

The paper's displayed standard-error formula, its equation (*), is

`s.e.(Ĉ_{in})² = Ĉ_{in}² ∑_k (σ̂_k²/f̂_k²) ( 1/(w_{ik} Ĉ_{ik}^α) + 1/∑_j w_{jk} C_{jk}^α )`,

and the recursion displayed immediately below it is

`s.e.(Ĉ_{i,k+1})² = Ĉ_{ik}² ( s.e.(F_{ik})² + s.e.(f̂_k)² ) + s.e.(Ĉ_{ik})² f̂_k²`,
`s.e.(F_{ik})² = σ̂_k²/(w_{ik} Ĉ_{ik}^α)`,  `s.e.(f̂_k)² = σ̂_k²/∑_j w_{jk} C_{jk}^α`.

## What is formalized here

* The weighted estimator family `fhatW`, `sigma2W`, the weighted projection
  `ChatW` and the weighted closed form `msepW` (equation (*)) as definitions,
  for an arbitrary weight function `w : ℕ → ℕ → ℝ` and arbitrary exponent
  `α : ℕ`. Mack's restriction `w_{ik} ∈ [0,1]` and `α ∈ {0,1,2}` is a modelling
  choice; no identity below uses it, so it is not imposed.
* `fhatW_eq_weighted_average`: `f̂_k` is the `w C^α`-weighted mean of the
  individual factors, generalizing `fhat_eq_weighted_average`.
* `weighted_sq_devW`, `weighted_sq_devW_at_fhatW`: the weighted
  sum-of-squares decomposition around `f̂_k`, generalizing
  `weighted_sq_dev` and `weighted_sq_dev_at_fhat`.
* `se2recW_eq_msepW`: the recursion displayed below (*), run for `i` steps,
  equals (*) itself, for every `α` and every weight function, whenever the
  weighted development factors along the row are nonzero. This is
  `se2rec_eq_msep` of `Recursion.lean` with the weights and the exponent
  carried through.
* `fhatW_unit`, `sigma2W_unit`, `msepW_unit`, `se2recW_unit`: at `α = 1` and
  unit weights every object above is the 1993 object of `ChainLadder.lean`,
  and `se2recW_eq_msep_unit` is then literally the statement of
  `se2rec_eq_msep`.
* `condExp_fhatWrv`: under (M1) in the `D_k` form, the weighted estimator is
  conditionally unbiased, `E[f̂^w_k | D_k] = f_k`, when the weights and the
  triangle entries of development year `k` are `D_k`-measurable. This
  generalizes `condExp_fhatRv`.
* `tailUltimate`, `tailSe2Step`: the tail factor of Section 3 as a convention.
  Mack leaves the tail parameters to the user, so these are definitions with no
  theorem attached.

Conventions are those of `ChainLadder.lean`: zero-based indices, `x / 0 = 0`.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-! ## The weighted estimator family -/

/-- Unit weights `w_{ik} = 1`, the case Mack's 1993 paper uses. -/
def unitWeights : ℕ → ℕ → ℝ := fun _ _ => 1

/-- Mack (1999): the weighted column sum `∑_{i ≤ n-k-2} w_{ik} C_{ik}^α`,
the denominator of the generalized development factor. -/
def SW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) : ℝ :=
  ∑ i ∈ contributors n k, w i k * C i k ^ α

/-- Mack (1999): the weighted numerator `∑_{i ≤ n-k-2} w_{ik} C_{ik}^α F_{ik}`. -/
def TW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) : ℝ :=
  ∑ i ∈ contributors n k, w i k * C i k ^ α * F C i k

/-- Mack (1999), the generalized development factor
`f̂_k = ∑_i w_{ik} C_{ik}^α F_{ik} / ∑_i w_{ik} C_{ik}^α`. -/
def fhatW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) : ℝ :=
  TW C n w α k / SW C n w α k

/-- Mack (1999), the generalized variance estimator
`σ̂_k² = (n-k-2)⁻¹ ∑_i w_{ik} C_{ik}^α (F_{ik} - f̂_k)²`, matching the
variance assumption `Var(F_{ik} | ⋯) = σ_k²/(w_{ik} C_{ik}^α)`. -/
def sigma2W (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) : ℝ :=
  (1 / ((n : ℝ) - k - 2)) *
    ∑ i ∈ contributors n k, w i k * C i k ^ α * (F C i k - fhatW C n w α k) ^ 2

/-- The projection of accident year `i` with the generalized factors,
`Ĉ_{ik} = C_{i,n-1-i} ∏_{j=n-1-i}^{k-1} f̂_j`. -/
def ChatW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i k : ℕ) : ℝ :=
  C i (n - 1 - i) * ∏ j ∈ Ico (n - 1 - i) k, fhatW C n w α j

/-- The generalized chain-ladder ultimate `Ĉ_{i,n-1}`. -/
def ultimateW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) : ℝ :=
  ChatW C n w α i (n - 1)

/-- One summand of Mack's 1999 formula (*):
`(σ̂_k²/f̂_k²) (1/(w_{ik} Ĉ_{ik}^α) + 1/∑_j w_{jk} C_{jk}^α)`. -/
def mackTermW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i k : ℕ) : ℝ :=
  (sigma2W C n w α k / fhatW C n w α k ^ 2) *
    (1 / (w i k * ChatW C n w α i k ^ α) + 1 / SW C n w α k)

/-- Mack (1999), formula (*): the standard error of the generalized
chain-ladder ultimate,
`s.e.(Ĉ_{in})² = Ĉ_{in}² ∑_{k=n-1-i}^{n-2} (σ̂_k²/f̂_k²) (1/(w_{ik} Ĉ_{ik}^α) + 1/∑_j w_{jk} C_{jk}^α)`.
At `α = 1` with unit weights this is `msep`. -/
def msepW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) : ℝ :=
  ultimateW C n w α i ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), mackTermW C n w α i k

/-- `m` steps of the recursion Mack (1999) displays below formula (*),
`s.e.(Ĉ_{i,k+1})² = Ĉ_{ik}² (σ̂_k²/(w_{ik} Ĉ_{ik}^α) + σ̂_k²/∑_j w_{jk} C_{jk}^α)
+ s.e.(Ĉ_{ik})² f̂_k²`, started at the latest observed development year
`n-1-i` with value `0`. -/
def se2recW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      let k := n - 1 - i + m
      ChatW C n w α i k ^ 2 *
          (sigma2W C n w α k / (w i k * ChatW C n w α i k ^ α)
            + sigma2W C n w α k / SW C n w α k)
        + se2recW C n w α i m * fhatW C n w α k ^ 2

/-! ## Deterministic identities -/

/-- **Weighted-average form.** `f̂_k` is the `w_{ik} C_{ik}^α`-weighted mean of
the individual factors `F_{ik}` (Mack 1999, the display defining `f̂_k`).
This generalizes `fhat_eq_weighted_average`; because the numerator `TW` is
written with the individual factors, no nonvanishing hypothesis is needed. -/
theorem fhatW_eq_weighted_average (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) :
    fhatW C n w α k
      = ∑ i ∈ contributors n k, (w i k * C i k ^ α / SW C n w α k) * F C i k := by
  unfold fhatW TW
  rw [sum_div]
  exact sum_congr rfl fun i _ => by ring

/-- Weighted sum-of-squares decomposition around an arbitrary centre `f`,
generalizing `weighted_sq_dev`. -/
theorem weighted_sq_devW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ) (f : ℝ) :
    ∑ i ∈ contributors n k, w i k * C i k ^ α * (F C i k - f) ^ 2
      = (∑ i ∈ contributors n k, w i k * C i k ^ α * F C i k ^ 2)
        - 2 * f * TW C n w α k + f ^ 2 * SW C n w α k := by
  unfold TW SW
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- At the generalized centre `f = f̂_k` the cross term collapses:
`∑ w C^α (F - f̂_k)² = ∑ w C^α F² - (∑ w C^α) f̂_k²`. This generalizes
`weighted_sq_dev_at_fhat` and is the identity behind the `n-k-2` degrees of
freedom of `sigma2W`. -/
theorem weighted_sq_devW_at_fhatW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α k : ℕ)
    (hS : SW C n w α k ≠ 0) :
    ∑ i ∈ contributors n k, w i k * C i k ^ α * (F C i k - fhatW C n w α k) ^ 2
      = (∑ i ∈ contributors n k, w i k * C i k ^ α * F C i k ^ 2)
        - SW C n w α k * fhatW C n w α k ^ 2 := by
  rw [weighted_sq_devW C n w α k _]
  unfold fhatW
  field_simp
  ring

/-- One step of the generalized projection: `Ĉ_{i,k+1} = Ĉ_{ik} f̂_k` for
`k ≥ n-1-i`. -/
theorem ChatW_succ (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i k : ℕ) (hk : n - 1 - i ≤ k) :
    ChatW C n w α i (k + 1) = ChatW C n w α i k * fhatW C n w α k := by
  unfold ChatW
  rw [prod_Ico_succ_top hk, mul_assoc]

/-- The generalized projection starts at the latest observed entry. -/
theorem ChatW_diag (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) :
    ChatW C n w α i (n - 1 - i) = C i (n - 1 - i) := by
  unfold ChatW
  simp

theorem msepW_eq_sum_mackTermW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) :
    msepW C n w α i
      = ultimateW C n w α i ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), mackTermW C n w α i k := rfl

/-! ## The recursion identity -/

/-- The algebra of one recursion step: with `A` the projection at `k`, `f` the
development factor, `B` the variance estimate, `P = w_{ik} Ĉ_{ik}^α` and `Sc`
the weighted column sum, one step of the recursion adds exactly the `k`-th
summand of formula (*) scaled by the *next* projection. Only `f ≠ 0` is used. -/
theorem se2recW_step (A B P Sc f X : ℝ) (hf : f ≠ 0) :
    A ^ 2 * (B / P + B / Sc) + A ^ 2 * X * f ^ 2
      = (A * f) ^ 2 * (X + B / f ^ 2 * (1 / P + 1 / Sc)) := by
  have hf2 : f ^ 2 ≠ 0 := pow_ne_zero 2 hf
  field_simp
  ring

/-- After `m` steps the generalized recursion equals formula (*) truncated at
development year `n-1-i+m`, for every exponent `α` and every weight function,
provided the generalized development factors used so far are nonzero. -/
theorem se2recW_eq_closed (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i m : ℕ)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhatW C n w α k ≠ 0) :
    se2recW C n w α i m
      = ChatW C n w α i (n - 1 - i + m) ^ 2
          * ∑ k ∈ Ico (n - 1 - i) (n - 1 - i + m), mackTermW C n w α i k := by
  induction m with
  | zero => simp [se2recW]
  | succ m ih =>
    have hf' : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhatW C n w α k ≠ 0 := by
      intro k hk
      exact hf k (Ico_subset_Ico_right (Nat.le_succ _) hk)
    have hfm : fhatW C n w α (n - 1 - i + m) ≠ 0 :=
      hf _ (mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.lt_succ_self _⟩)
    rw [se2recW, ih hf', show n - 1 - i + (m + 1) = n - 1 - i + m + 1 from rfl,
      sum_Ico_succ_top (Nat.le_add_right _ _), ChatW_succ C n w α i _ (Nat.le_add_right _ _)]
    unfold mackTermW
    exact se2recW_step _ _ _ _ _ _ hfm

/-- **Mack (1999): the recursion equals formula (*), for general weights and
general exponent.** For accident year `i ≤ n-1`, `i` steps of the recursion
displayed below Mack's (*) return exactly (*) itself, whenever the generalized
development factors along the row are nonzero. At `α = 1` with unit weights
this is `se2rec_eq_msep`, i.e. Mack 1993. -/
theorem se2recW_eq_msepW (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhatW C n w α k ≠ 0) :
    se2recW C n w α i i = msepW C n w α i := by
  have hd : n - 1 - i + i = n - 1 := Nat.sub_add_cancel hi
  rw [msepW_eq_sum_mackTermW, se2recW_eq_closed C n w α i i (by rwa [hd]), hd]
  rfl

/-! ## The 1993 case: `α = 1`, unit weights -/

theorem SW_unit (C : ℕ → ℕ → ℝ) (n k : ℕ) : SW C n unitWeights 1 k = S C n k := by
  unfold SW S unitWeights
  exact sum_congr rfl fun i _ => by ring

theorem TW_unit (C : ℕ → ℕ → ℝ) (n k : ℕ) (h : ∀ i ∈ contributors n k, C i k ≠ 0) :
    TW C n unitWeights 1 k = T C n k := by
  unfold TW T unitWeights F
  refine sum_congr rfl fun i hi => ?_
  field_simp [h i hi]

/-- At `α = 1` with unit weights the generalized factor is the 1993 factor. -/
theorem fhatW_unit (C : ℕ → ℕ → ℝ) (n k : ℕ) (h : ∀ i ∈ contributors n k, C i k ≠ 0) :
    fhatW C n unitWeights 1 k = fhat C n k := by
  unfold fhatW fhat
  rw [TW_unit C n k h, SW_unit C n k]

/-- At `α = 1` with unit weights the generalized variance estimator is
Mack's 1993 `σ̂_k²`. -/
theorem sigma2W_unit (C : ℕ → ℕ → ℝ) (n k : ℕ) (h : ∀ i ∈ contributors n k, C i k ≠ 0) :
    sigma2W C n unitWeights 1 k = sigma2 C n k := by
  unfold sigma2W sigma2
  rw [fhatW_unit C n k h]
  refine congrArg _ (sum_congr rfl fun i _ => ?_)
  unfold unitWeights
  ring

/-- At `α = 1` with unit weights the generalized projection is the 1993
projection. -/
theorem ChatW_unit (C : ℕ → ℕ → ℝ) (n i k : ℕ)
    (hC : ∀ j, ∀ l ∈ contributors n j, C l j ≠ 0) :
    ChatW C n unitWeights 1 i k = Chat C n i k := by
  unfold ChatW Chat
  rw [prod_congr rfl fun j _ => fhatW_unit C n j (hC j)]

theorem ultimateW_unit (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (hC : ∀ j, ∀ l ∈ contributors n j, C l j ≠ 0) :
    ultimateW C n unitWeights 1 i = ultimate C n i :=
  ChatW_unit C n i (n - 1) hC

theorem mackTermW_unit (C : ℕ → ℕ → ℝ) (n i k : ℕ)
    (hC : ∀ j, ∀ l ∈ contributors n j, C l j ≠ 0) :
    mackTermW C n unitWeights 1 i k = mackTerm C n i k := by
  unfold mackTermW mackTerm
  rw [sigma2W_unit C n k (hC k), fhatW_unit C n k (hC k), ChatW_unit C n i k hC, SW_unit C n k]
  norm_num [unitWeights]

/-- **Mack 1999 formula (*) at `α = 1`, unit weights, is Mack 1993.** -/
theorem msepW_unit (C : ℕ → ℕ → ℝ) (n i : ℕ)
    (hC : ∀ j, ∀ l ∈ contributors n j, C l j ≠ 0) :
    msepW C n unitWeights 1 i = msep C n i := by
  rw [msepW_eq_sum_mackTermW, msep_eq_sum_mackTerm, ultimateW_unit C n i hC,
    sum_congr rfl fun k _ => mackTermW_unit C n i k hC]

/-- **The generalized recursion at `α = 1`, unit weights, is the 1993
recursion of `Recursion.lean`.** -/
theorem se2recW_unit (C : ℕ → ℕ → ℝ) (n i m : ℕ)
    (hC : ∀ j, ∀ l ∈ contributors n j, C l j ≠ 0) :
    se2recW C n unitWeights 1 i m = se2rec C n i m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [se2recW, se2rec, ih]
    simp only [unitWeights]
    rw [sigma2W_unit C n _ (hC _), fhatW_unit C n _ (hC _), ChatW_unit C n i _ hC, SW_unit C n _]
    norm_num

/-- **The general theorem specializes to `se2rec_eq_msep`.** At `α = 1` with
unit weights, `i` steps of Mack's 1999 recursion return Mack's 1993 estimator
of the mean squared error of prediction. -/
theorem se2recW_eq_msep_unit (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hC : ∀ j, ∀ l ∈ contributors n j, C l j ≠ 0)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0) :
    se2recW C n unitWeights 1 i i = msep C n i := by
  rw [se2recW_eq_msepW C n unitWeights 1 i hi (by
        intro k hk
        rw [fhatW_unit C n k (hC k)]
        exact hf k hk),
    msepW_unit C n i hC]

/-! ## The tail factor (Mack 1999, Section 3)

Mack's Section 3 attaches a tail factor to the ultimate. The tail factor
itself, and the variance parameters attached to it, are supplied by the
actuary: the paper gives no estimator for them, only the arithmetic of
carrying them through the recursion. They are therefore definitions here, and
no theorem in this development uses them. -/

/-- Mack (1999), Section 3: the ultimate extended by a tail factor,
`Ĉ_{i,∞} = Ĉ_{i,n-1} · f_tail`. The tail factor is a convention supplied by
the actuary; nothing is proved about it. -/
def tailUltimate (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ) (ftail : ℝ) : ℝ :=
  ultimateW C n w α i * ftail

/-- Mack (1999), Section 3: one further step of the recursion with
actuary-supplied tail parameters `f_tail`, `σ²_tail` and a tail analogue
`S_tail` of the weighted column sum. Mack leaves the choice of all three
open, so this is a convention, not an estimator; nothing is proved about it. -/
def tailSe2Step (C : ℕ → ℕ → ℝ) (n : ℕ) (w : ℕ → ℕ → ℝ) (α i : ℕ)
    (ftail sigma2tail Stail : ℝ) : ℝ :=
  ultimateW C n w α i ^ 2
      * (sigma2tail / (w i (n - 1) * ultimateW C n w α i ^ α) + sigma2tail / Stail)
    + se2recW C n w α i i * ftail ^ 2

end

/-! ## Stochastic layer: conditional unbiasedness of the weighted estimator -/

open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- The weighted column sum `∑_i w_{ik} C_{ik}^α` as a random variable. -/
def RandomTriangle.SWrv (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) : Ω → ℝ :=
  fun ω => SW (X.at ω) n (fun i k => w i k ω) α k

/-- Mack's 1999 weighted development factor as a random variable. -/
def RandomTriangle.fhatWrv (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) : Ω → ℝ :=
  fun ω => fhatW (X.at ω) n (fun i k => w i k ω) α k

/-- The `D_k`-measurable multiplier of `C_{i,k+1}` inside `f̂^w_k`, namely
`w_{ik} C_{ik}^α / C_{ik}`. For `α = 1` and unit weights it is `1`; writing it
this way keeps `α = 0` (where the multiplier is `1/C_{ik}`) in range. -/
def RandomTriangle.gW (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α i k : ℕ) : Ω → ℝ :=
  fun ω => w i k ω * X.C i k ω ^ α / X.C i k ω

theorem RandomTriangle.SWrv_eq_sum (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) :
    X.SWrv w α k = ∑ i ∈ contributors n k, (w i k * X.C i k ^ α) := by
  ext ω
  simp [RandomTriangle.SWrv, SW, RandomTriangle.at, Finset.sum_apply]

/-- The weighted column sum is `D_k`-measurable when the weights are. -/
theorem RandomTriangle.stronglyMeasurable_SWrv (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ)
    (α k : ℕ) (hw : ∀ i, StronglyMeasurable[X.D k] (w i k)) :
    StronglyMeasurable[X.D k] (X.SWrv w α k) := by
  rw [X.SWrv_eq_sum]
  refine Finset.stronglyMeasurable_sum _ fun i _ => ?_
  exact ((hw i).measurable.mul ((X.meas i k k le_rfl).measurable.pow_const α)).stronglyMeasurable

/-- The multiplier `w_{ik} C_{ik}^α / C_{ik}` is `D_k`-measurable. -/
theorem RandomTriangle.stronglyMeasurable_gW (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ)
    (α i k : ℕ) (hw : StronglyMeasurable[X.D k] (w i k)) :
    StronglyMeasurable[X.D k] (X.gW w α i k) := by
  have hC : StronglyMeasurable[X.D k] (X.C i k) := X.meas i k k le_rfl
  exact ((hw.measurable.mul (hC.measurable.pow_const α)).div hC.measurable).stronglyMeasurable

/-- `f̂^w_k = (∑_i w_{ik} C_{ik}^α)⁻¹ ∑_i (w_{ik} C_{ik}^α / C_{ik}) C_{i,k+1}`:
the weighted estimator is a `D_k`-measurable linear combination of the next
column, which is what makes (M1) applicable. -/
theorem RandomTriangle.fhatWrv_eq (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α k : ℕ) :
    X.fhatWrv w α k
      = (fun ω => (X.SWrv w α k ω)⁻¹)
          * ∑ i ∈ contributors n k, X.gW w α i k * X.C i (k + 1) := by
  ext ω
  have h : ∀ i, w i k ω * X.C i k ω ^ α * (X.C i (k + 1) ω / X.C i k ω)
      = w i k ω * X.C i k ω ^ α / X.C i k ω * X.C i (k + 1) ω := fun i => by ring
  simp only [RandomTriangle.fhatWrv, RandomTriangle.SWrv, RandomTriangle.gW,
    RandomTriangle.at, fhatW, TW, F, Pi.mul_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => h i), div_eq_inv_mul]

/-- **Conditional unbiasedness of Mack's 1999 weighted estimator.** Under (M1)
in the `D_k` form, with `D_k`-measurable weights and on the event that the
weighted column sum is nonzero, `E[f̂^w_k | D_k] = f_k` for every exponent `α`.
The hypothesis `C_{ik} ≠ 0` on the contributing entries is what the individual
factors `F_{ik}` need in any case, and is what makes the multiplier
`w_{ik} C_{ik}^α / C_{ik}` recover `w_{ik} C_{ik}^α` when it meets `C_{ik}`
(for `α = 0` it cannot be dispensed with). This generalizes `condExp_fhatRv`,
which is the case `α = 1` with unit weights. -/
theorem condExp_fhatWrv (X : RandomTriangle Ω n) (w : ℕ → ℕ → Ω → ℝ) (α : ℕ) (f : ℕ → ℝ)
    (k : ℕ)
    (hw : ∀ i, StronglyMeasurable[X.D k] (w i k))
    (hM : Mack1 X μ f)
    (hC0 : ∀ᵐ ω ∂μ, ∀ i ∈ contributors n k, X.C i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ, X.SWrv w α k ω ≠ 0)
    (hCint : ∀ i ∈ contributors n k, Integrable (X.C i (k + 1)) μ)
    (hgint : ∀ i ∈ contributors n k, Integrable (X.gW w α i k * X.C i (k + 1)) μ)
    (hfint : Integrable (X.fhatWrv w α k) μ) :
    μ[X.fhatWrv w α k | X.D k] =ᵐ[μ] fun _ => f k := by
  set Tk : Ω → ℝ := ∑ i ∈ contributors n k, X.gW w α i k * X.C i (k + 1) with hTk
  have hTint : Integrable Tk μ :=
    (integrable_finsetSum _ hgint).congr
      (Eventually.of_forall fun ω => (Finset.sum_apply ω _ _).symm)
  have hinv : StronglyMeasurable[X.D k] (fun ω => (X.SWrv w α k ω)⁻¹) :=
    (((X.stronglyMeasurable_SWrv w α k hw).measurable.inv)).stronglyMeasurable
  have hprod : Integrable ((fun ω => (X.SWrv w α k ω)⁻¹) * Tk) μ := by
    rw [← X.fhatWrv_eq]; exact hfint
  have h1 : μ[X.fhatWrv w α k | X.D k]
      =ᵐ[μ] (fun ω => (X.SWrv w α k ω)⁻¹) * μ[Tk | X.D k] := by
    rw [X.fhatWrv_eq]
    exact condExp_mul_of_stronglyMeasurable_left hinv hprod hTint
  -- (M1) evaluates each summand
  have hterm : ∀ i ∈ contributors n k,
      μ[X.gW w α i k * X.C i (k + 1) | X.D k]
        =ᵐ[μ] fun ω => X.gW w α i k ω * (f k * X.C i k ω) := by
    intro i hi
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (X.stronglyMeasurable_gW w α i k (hw i)) (hgint i hi) (hCint i hi)
    refine hpull.trans ?_
    filter_upwards [hM i (lt_of_mem_contributors hi) k] with ω hω
    simp [Pi.mul_apply, hω]
  have h2 : μ[Tk | X.D k] =ᵐ[μ] fun ω => f k * X.SWrv w α k ω := by
    have hsum := condExp_finsetSum (μ := μ) (m := X.D k) (s := contributors n k)
      (f := fun i => X.gW w α i k * X.C i (k + 1)) (fun i hi => hgint i hi)
    refine hsum.trans ?_
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ contributors n k,
        (μ[X.gW w α i k * X.C i (k + 1) | X.D k]) ω
          = X.gW w α i k ω * (f k * X.C i k ω) := by
      rw [eventually_all_finset]
      exact hterm
    filter_upwards [hall, hC0] with ω hω hC0ω
    rw [Finset.sum_apply, Finset.sum_congr rfl fun i hi => hω i hi, X.SWrv_eq_sum,
      Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : X.C i k ω ≠ 0 := hC0ω i hi
    simp only [RandomTriangle.gW, Pi.mul_apply, Pi.pow_apply]
    field_simp
  refine h1.trans ?_
  filter_upwards [h2, hS] with ω hω hSω
  simp only [Pi.mul_apply, hω]
  field_simp

end

end VerifiedReserving
