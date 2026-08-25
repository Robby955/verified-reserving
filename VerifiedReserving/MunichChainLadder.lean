import VerifiedReserving.ChainLadder

/-!
# The separate-chain-ladder paid/incurred gap identity

Quarg and Mack, *Munich Chain Ladder: A Reserving Method that Reduces the
Gap between IBNR Projections Based on Paid Losses and IBNR Projections Based
on Incurred Losses* (2004), Section 1.1.2, consider the two quadrangles obtained
by applying chain ladder separately to cumulative paid and incurred triangles.

If `(P/I)_{i,t}` is the paid-to-incurred ratio of accident year `i` at
development year `t`, and `(P/I)_t` is the ratio of the paid and incurred
column totals, their fundamental identity is

`(P/I)_{i,t} / (P/I)_t = (P/I)_{i,d} / (P/I)_d`,

where `d` is the latest observed development year of row `i`. Thus separate
chain-ladder projections preserve each row's paid-to-incurred ratio relative
to the corresponding column ratio. This deterministic module proves that
identity from the chain-ladder definitions in `ChainLadder.lean`.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- The quadrangle obtained by retaining the observed cells of `C` and filling
each future cell with its separate chain-ladder projection. -/
def sclQuadrangle (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  if k ≤ n - 1 - i then C i k else Chat C n i k

/-- The total of development column `k` in the separate-chain-ladder
quadrangle. Quarg and Mack average P/I ratios with incurred amounts, which is
equivalently the ratio of the paid and incurred column totals. -/
def sclColumnTotal (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ i ∈ range n, sclQuadrangle C n i k

/-- Paid-to-incurred ratio `(P/I)_{i,k}`. -/
def paidIncurredRatio (P I : ℕ → ℕ → ℝ) (i k : ℕ) : ℝ :=
  P i k / I i k

/-- Average paid-to-incurred ratio at development year `k`, weighted by the
incurred amounts: `(∑_i P_{i,k}) / (∑_i I_{i,k})`. -/
def averagePaidIncurredRatio (P I : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  (∑ i ∈ range n, P i k) / ∑ i ∈ range n, I i k

/-- Every completed column total advances by the original triangle's
chain-ladder factor. This is the column-total calculation in Quarg and Mack
(2004), Section 1.1.2, p. 272. -/
theorem sclColumnTotal_succ (C : ℕ → ℕ → ℝ) (n k : ℕ)
    (_hk : k < n - 1) (hS : S C n k ≠ 0) :
    sclColumnTotal C n (k + 1) = sclColumnTotal C n k * fhat C n k := by
  have hsplit : n - k - 1 ≤ n := by omega
  have hscl_eq_Chat (i m : ℕ) (hm : n - 1 - i ≤ m) :
      sclQuadrangle C n i m = Chat C n i m := by
    unfold sclQuadrangle
    split
    case isTrue h =>
      have heq : m = n - 1 - i := Nat.le_antisymm h hm
      subst m
      exact (Chat_diag C n i).symm
    case isFalse => rfl
  have hobs : ∑ i ∈ range (n - k - 1), sclQuadrangle C n i k = S C n k := by
    unfold S contributors
    refine sum_congr rfl fun i hi => ?_
    unfold sclQuadrangle
    rw [if_pos]
    have hi' := mem_range.mp hi
    omega
  have hobs_succ :
      ∑ i ∈ range (n - k - 1), sclQuadrangle C n i (k + 1) = T C n k := by
    unfold T contributors
    refine sum_congr rfl fun i hi => ?_
    unfold sclQuadrangle
    rw [if_pos]
    have hi' := mem_range.mp hi
    omega
  have htail :
      ∑ i ∈ Ico (n - k - 1) n, sclQuadrangle C n i (k + 1) =
        (∑ i ∈ Ico (n - k - 1) n, sclQuadrangle C n i k) * fhat C n k := by
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_Ico.mp hi
    have hd : n - 1 - i ≤ k := by omega
    rw [hscl_eq_Chat i (k + 1) (by omega), hscl_eq_Chat i k hd,
      Chat_succ C n i k hd]
  have hT : T C n k = S C n k * fhat C n k := by
    unfold fhat
    field_simp
  unfold sclColumnTotal
  rw [← sum_range_add_sum_Ico (fun i => sclQuadrangle C n i (k + 1)) hsplit,
    ← sum_range_add_sum_Ico (fun i => sclQuadrangle C n i k) hsplit,
    hobs_succ, hobs, htail, hT, add_mul]

/-- Iterating `sclColumnTotal_succ`, when each factor denominator is nonzero,
a completed column total at `t` is its value at `d` times the product of the
separate chain-ladder factors from `d` to `t`. -/
theorem sclColumnTotal_eq_mul_prod (C : ℕ → ℕ → ℝ) (n d t : ℕ)
    (hdt : d ≤ t) (ht : t < n)
    (hS : ∀ k ∈ Ico d t, S C n k ≠ 0) :
    sclColumnTotal C n t =
      sclColumnTotal C n d * ∏ k ∈ Ico d t, fhat C n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdt
  revert ht hS
  induction m with
  | zero =>
    intro _ht _hS
    simp
  | succ m ih =>
    intro ht hS
    have hlast : d + m ∈ Ico d (d + (m + 1)) := by
      exact mem_Ico.mpr ⟨Nat.le_add_right d m, by omega⟩
    have hSm : S C n (d + m) ≠ 0 := hS _ hlast
    have hk : d + m < n - 1 := by omega
    have hS' : ∀ k ∈ Ico d (d + m), S C n k ≠ 0 := by
      intro k hk'
      exact hS k (Ico_subset_Ico_right (Nat.le_succ _) hk')
    rw [show d + (m + 1) = d + m + 1 by omega,
      sclColumnTotal_succ C n (d + m) hk hSm,
      ih (Nat.le_add_right d m) (by omega) hS',
      prod_Ico_succ_top (Nat.le_add_right d m), mul_assoc]

/-- **Quarg-Mack separate-chain-ladder gap identity.** For a future
development year `t`, the paid-to-incurred ratio of a row divided by the
paid-to-incurred ratio of the column totals is its value at the row's latest
observed development year. This is the boxed identity in Quarg and Mack
(2004), Section 1.1.2, p. 272. -/
theorem quargMack_gap_identity
    (P I : ℕ → ℕ → ℝ) (n i t : ℕ)
    (_hi : i < n) (ht : n - 1 - i < t) (htn : t < n)
    (hfP : ∀ k ∈ Ico (n - 1 - i) t, fhat P n k ≠ 0)
    (hfI : ∀ k ∈ Ico (n - 1 - i) t, fhat I n k ≠ 0)
    (hIrow : I i (n - 1 - i) ≠ 0)
    (hPcol : sclColumnTotal P n (n - 1 - i) ≠ 0)
    (hIcol : sclColumnTotal I n (n - 1 - i) ≠ 0) :
    paidIncurredRatio (sclQuadrangle P n) (sclQuadrangle I n) i t /
        averagePaidIncurredRatio (sclQuadrangle P n) (sclQuadrangle I n) n t =
      paidIncurredRatio (sclQuadrangle P n) (sclQuadrangle I n) i (n - 1 - i) /
        averagePaidIncurredRatio (sclQuadrangle P n) (sclQuadrangle I n) n
          (n - 1 - i) := by
  let d := n - 1 - i
  have hdt : d ≤ t := Nat.le_of_lt ht
  have hSP : ∀ k ∈ Ico d t, S P n k ≠ 0 := by
    intro k hk
    exact (div_ne_zero_iff.mp (hfP k hk)).2
  have hSI : ∀ k ∈ Ico d t, S I n k ≠ 0 := by
    intro k hk
    exact (div_ne_zero_iff.mp (hfI k hk)).2
  have hPtotal := sclColumnTotal_eq_mul_prod P n d t hdt htn hSP
  have hItotal := sclColumnTotal_eq_mul_prod I n d t hdt htn hSI
  have hProw : sclQuadrangle P n i t = P i d * ∏ k ∈ Ico d t, fhat P n k := by
    unfold sclQuadrangle Chat
    rw [if_neg (not_le_of_gt ht)]
  have hIrow' : sclQuadrangle I n i t = I i d * ∏ k ∈ Ico d t, fhat I n k := by
    unfold sclQuadrangle Chat
    rw [if_neg (not_le_of_gt ht)]
  have hPdiag : sclQuadrangle P n i d = P i d := by
    simp [sclQuadrangle, d]
  have hIdiag : sclQuadrangle I n i d = I i d := by
    simp [sclQuadrangle, d]
  have hpP : ∏ k ∈ Ico d t, fhat P n k ≠ 0 := prod_ne_zero_iff.mpr hfP
  have hpI : ∏ k ∈ Ico d t, fhat I n k ≠ 0 := prod_ne_zero_iff.mpr hfI
  have hIrow_t : sclQuadrangle I n i t ≠ 0 := by
    rw [hIrow']
    exact mul_ne_zero hIrow hpI
  have hPtotal_t : sclColumnTotal P n t ≠ 0 := by
    rw [hPtotal]
    exact mul_ne_zero hPcol hpP
  have hItotal_t : sclColumnTotal I n t ≠ 0 := by
    rw [hItotal]
    exact mul_ne_zero hIcol hpI
  change
    (sclQuadrangle P n i t / sclQuadrangle I n i t) /
        (sclColumnTotal P n t / sclColumnTotal I n t) =
      (sclQuadrangle P n i d / sclQuadrangle I n i d) /
        (sclColumnTotal P n d / sclColumnTotal I n d)
  rw [hProw, hIrow', hPtotal, hItotal, hPdiag, hIdiag]
  field_simp [hpP, hpI, hIrow, hPcol, hIcol, hIrow_t, hPtotal_t, hItotal_t]

end

end VerifiedReserving
