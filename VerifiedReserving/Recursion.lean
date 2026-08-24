import VerifiedReserving.ChainLadder

/-!
# Mack (1999): the recursive form of the standard error equals the 1993 closed form

Mack, ASTIN Bulletin 29 (1999) 361-366, rewrites the 1993 estimator as a
recursion along the row of accident year `i`, starting from `0` on the
latest diagonal:

`s.e.(Ĉ_{i,k+1})² = Ĉ_{i,k}² (s.e.(F_{i,k})² + s.e.(f̂_k)²) + s.e.(Ĉ_{i,k})² f̂_k²`

with, for `α = 1` and unit weights, `s.e.(F_{i,k})² = σ̂_k² / Ĉ_{i,k}` and
`s.e.(f̂_k)² = σ̂_k² / S_k`. The paper states that the recursion "leads to"
the 1993 closed form. This file proves that statement: after `i` steps the
recursion returns exactly `msep` as defined in `ChainLadder.lean`, provided
the development factors along the row are nonzero. This is catalogue row 1
of the variant catalogue: Mack 1999 (α = 1) is literally equal to Mack 1993.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- `m` steps of Mack's 1999 recursion for accident year `i`, starting at the
latest observed development year `d = n-1-i` with value `0`. -/
def se2rec (C : ℕ → ℕ → ℝ) (n i : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      let k := n - 1 - i + m
      Chat C n i k ^ 2 * (sigma2 C n k / Chat C n i k + sigma2 C n k / S C n k)
        + se2rec C n i m * fhat C n k ^ 2

/-- The one-step summand of the 1993 closed form. -/
def mackTerm (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  (sigma2 C n k / (fhat C n k) ^ 2) * (1 / Chat C n i k + 1 / S C n k)

theorem msep_eq_sum_mackTerm (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    msep C n i = (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1), mackTerm C n i k := by
  rfl

/-- After `m` steps the recursion equals the closed form truncated at
development year `d + m`. -/
theorem se2rec_eq_closed (C : ℕ → ℕ → ℝ) (n i : ℕ) (m : ℕ)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhat C n k ≠ 0) :
    se2rec C n i m
      = Chat C n i (n - 1 - i + m) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1 - i + m), mackTerm C n i k := by
  induction m with
  | zero => simp [se2rec]
  | succ m ih =>
    have hf' : ∀ k ∈ Ico (n - 1 - i) (n - 1 - i + m), fhat C n k ≠ 0 := by
      intro k hk
      exact hf k (Ico_subset_Ico_right (Nat.le_succ _) hk)
    have hfm : fhat C n (n - 1 - i + m) ≠ 0 :=
      hf _ (mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.lt_succ_self _⟩)
    rw [se2rec, ih hf', show n - 1 - i + (m + 1) = n - 1 - i + m + 1 from rfl,
      sum_Ico_succ_top (Nat.le_add_right _ _), Chat_succ C n i _ (Nat.le_add_right _ _)]
    unfold mackTerm
    have hf2 : fhat C n (n - 1 - i + m) ^ 2 ≠ 0 := pow_ne_zero 2 hfm
    field_simp
    ring

/-- **Mack 1999 = Mack 1993.** For accident year `i ≤ n-1`, `i` steps of the
1999 recursion (α = 1, unit weights) return exactly the 1993 estimator of the
mean squared error of prediction, whenever the development factors along the
row are nonzero. -/
theorem se2rec_eq_msep (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i ≤ n - 1)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0) :
    se2rec C n i i = msep C n i := by
  have hd : n - 1 - i + i = n - 1 := Nat.sub_add_cancel hi
  rw [msep_eq_sum_mackTerm, se2rec_eq_closed C n i i (by rwa [hd]), hd]
  rfl

end

end VerifiedReserving
