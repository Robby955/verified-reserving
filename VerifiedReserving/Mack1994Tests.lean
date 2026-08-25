import VerifiedReserving.ChainLadder

/-!
# Mack's 1994 diagnostic tests

This file formalizes the deterministic statistics in Appendices G and H of
Mack (1994), "Measuring the Variability of Chain Ladder Reserve Estimates."
The Spearman statistic checks adjacent development-factor columns. The
calendar-year statistic checks whether small or large factors collect on
calendar diagonals.

The rank and counting statistics are definitions on any triangle. Their null
calibrations require extra rank-distribution assumptions that do not follow
from Mack's chain-ladder moment assumptions. Exact finite calculations prove
the single Spearman mean and variance and Mack's calendar formulas (H1)-(H2).
The aggregate variance and Normal acceptance rules remain nominal definitions.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-! ## Adjacent development-factor ranks -/

/-- The one-based strict rank of `x i` among the indices in `s`. Tied values
receive the same rank. Mack (1994), Appendix G, p. 157, uses ordinary ranks
and does not specify a tie correction; the null calibration presumes no ties. -/
def rankOn (s : Finset ℕ) (x : ℕ → ℝ) (i : ℕ) : ℕ :=
  (s.filter fun j => x j < x i).card + 1

/-- The accident years common to factor columns `k - 1` and `k`.
This is the zero-based form of `1 ≤ i ≤ I-k` in Mack (1994), Appendix G,
equation (G4), p. 157. -/
def adjacentFactorRows (n k : ℕ) : Finset ℕ := contributors n k

/-- Rank of development factor `F i k` after restricting to `rows`.
The restriction matters for the earlier of the two columns: its last
observation is omitted before reranking, as required before Mack (1994),
equation (G4), p. 157. -/
def factorRankOn (C : ℕ → ℕ → ℝ) (rows : Finset ℕ) (k i : ℕ) : ℕ :=
  rankOn rows (fun j => F C j k) i

/-- Spearman's rank correlation coefficient for factor columns `k - 1` and
`k`, Mack (1994), Appendix G, equation (G4), p. 157. It is meaningful for
`1 ≤ k`, at least two common rows, and untied factors. -/
def spearmanAdjacent (C : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  let rows := adjacentFactorRows n k
  let q : ℝ := rows.card
  1 - 6 * (∑ i ∈ rows,
    ((factorRankOn C rows k i : ℝ) - (factorRankOn C rows (k - 1) i : ℝ)) ^ 2) /
      (q ^ 3 - q)

/-- Mack's triangle-wide development-factor correlation statistic, the
inverse-null-variance weighted average in Mack (1994), Appendix G,
equation (G5), p. 158. -/
def developmentCorrelationTest (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  let ks := Ico 1 (n - 2)
  let weight := fun k => ((adjacentFactorRows n k).card : ℝ) - 1
  (∑ k ∈ ks, weight k * spearmanAdjacent C n k) / ∑ k ∈ ks, weight k

/-- Arithmetic mean over the uniform distribution on a finite type. -/
private def finiteUniformMean {Ω : Type*} [Fintype Ω] (X : Ω → ℚ) : ℚ :=
  (∑ ω, X ω) / Fintype.card Ω

/-- Variance under the uniform distribution on a finite type. -/
private def finiteUniformVariance {Ω : Type*} [Fintype Ω] (X : Ω → ℚ) : ℚ :=
  finiteUniformMean (fun ω => (X ω - finiteUniformMean X) ^ 2)

private lemma finiteUniformMean_perm_mulRight {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α → ℚ) (τ : Equiv.Perm α) :
    finiteUniformMean (fun σ => f (σ * τ)) = finiteUniformMean f := by
  unfold finiteUniformMean
  change (∑ σ, f ((Equiv.mulRight τ) σ)) / _ = _
  rw [Equiv.sum_comp (Equiv.mulRight τ)]

private lemma finiteUniformMean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (f : Ω → ι → ℚ) :
    finiteUniformMean (fun ω => ∑ i, f ω i) =
      ∑ i, finiteUniformMean (fun ω => f ω i) := by
  simp only [finiteUniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]

private lemma finiteUniformMean_finsetSum {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (f : Ω → ι → ℚ) :
    finiteUniformMean (fun ω => ∑ i ∈ s, f ω i) =
      ∑ i ∈ s, finiteUniformMean (fun ω => f ω i) := by
  unfold finiteUniformMean
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

private lemma finiteUniformMean_mul_const {Ω : Type*} [Fintype Ω]
    (X : Ω → ℚ) (c : ℚ) :
    finiteUniformMean (fun ω => X ω * c) = finiteUniformMean X * c := by
  unfold finiteUniformMean
  change (∑ ω, X ω * c) / _ = (∑ ω, X ω) / _ * c
  have hsum : (∑ ω, X ω * c) = (∑ ω, X ω) * c := by
    simpa using (Finset.sum_mul Finset.univ X c).symm
  rw [hsum]
  ring

private lemma finiteUniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    finiteUniformMean (fun _ : Ω => c) = c := by
  simp [finiteUniformMean, Fintype.card_ne_zero]

private lemma finiteUniformMean_neg {Ω : Type*} [Fintype Ω] (X : Ω → ℚ) :
    finiteUniformMean (fun ω => -X ω) = -finiteUniformMean X := by
  simpa only [mul_neg, mul_one] using finiteUniformMean_mul_const X (-1)

private lemma perm_coordinateMean_eq {α : Type*} [Fintype α] [DecidableEq α]
    (y : α → ℚ) (i j : α) :
    finiteUniformMean (fun σ : Equiv.Perm α => y (σ i)) =
      finiteUniformMean (fun σ : Equiv.Perm α => y (σ j)) := by
  simpa [Equiv.Perm.mul_apply] using
    (finiteUniformMean_perm_mulRight
      (f := fun σ : Equiv.Perm α => y (σ i)) (Equiv.swap i j)).symm

private lemma perm_coordinateMean_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (y : α → ℚ) (hy : ∑ i, y i = 0) (i : α) :
    finiteUniformMean (fun σ : Equiv.Perm α => y (σ i)) = 0 := by
  have hpoint (σ : Equiv.Perm α) : ∑ j, y (σ j) = 0 := by
    rw [Equiv.sum_comp σ]
    exact hy
  have htotal :
      (∑ j, finiteUniformMean (fun σ : Equiv.Perm α => y (σ j))) = 0 := by
    rw [← finiteUniformMean_sum]
    simp_rw [hpoint]
    simp [finiteUniformMean]
  have hcard :
      (Fintype.card α : ℚ) *
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i)) = 0 := by
    rw [← htotal]
    simp_rw [perm_coordinateMean_eq y _ i]
    simp
  have hcard_ne : (Fintype.card α : ℚ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hcard).resolve_left hcard_ne

private lemma perm_coordinateMean {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (g : α → ℚ) (i : α) :
    finiteUniformMean (fun σ : Equiv.Perm α => g (σ i)) =
      (∑ a, g a) / Fintype.card α := by
  have hpoint (σ : Equiv.Perm α) : ∑ j, g (σ j) = ∑ a, g a := by
    rw [Equiv.sum_comp σ]
  have htotal :
      (∑ j, finiteUniformMean (fun σ : Equiv.Perm α => g (σ j))) = ∑ a, g a := by
    rw [← finiteUniformMean_sum]
    simp_rw [hpoint]
    exact finiteUniformMean_const _
  have hcard :
      (Fintype.card α : ℚ) *
          finiteUniformMean (fun σ : Equiv.Perm α => g (σ i)) = ∑ a, g a := by
    rw [← htotal]
    simp_rw [perm_coordinateMean_eq g _ i]
    simp
  have hcard_ne : (Fintype.card α : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hcard_ne).2
  simpa [mul_comm] using hcard

private lemma perm_crossMean_eq {α : Type*} [Fintype α] [DecidableEq α]
    (y : α → ℚ) (i j k : α) (hij : i ≠ j) (hik : i ≠ k) :
    finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) =
      finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ k)) := by
  simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik] using
    (finiteUniformMean_perm_mulRight
      (f := fun σ : Equiv.Perm α => y (σ i) * y (σ j))
      (Equiv.swap j k)).symm

private lemma perm_crossMean_of_sum_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (y : α → ℚ) (hy : ∑ a, y a = 0)
    (i j : α) (hij : i ≠ j) (hcard : 2 ≤ Fintype.card α) :
    finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) =
      -finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) ^ 2) /
        (Fintype.card α - 1 : ℕ) := by
  have hpoint (σ : Equiv.Perm α) :
      (∑ k ∈ Finset.univ.erase i, y (σ i) * y (σ k)) = -y (σ i) ^ 2 := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    rw [Equiv.sum_comp σ, hy]
    ring
  have htotal :
      (∑ k ∈ Finset.univ.erase i,
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ k))) =
        -finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) ^ 2) := by
    rw [← finiteUniformMean_finsetSum]
    simp_rw [hpoint]
    exact finiteUniformMean_neg _
  have hequal :
      (∑ k ∈ Finset.univ.erase i,
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ k))) =
        (Fintype.card α - 1 : ℕ) *
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) := by
    calc
      _ = ∑ _k ∈ Finset.univ.erase i,
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hki : k ≠ i := (Finset.mem_erase.mp hk).1
            exact perm_crossMean_eq y i k j hki.symm hij
      _ = _ := by
        rw [Finset.sum_const]
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
  have hmul :
      (Fintype.card α - 1 : ℕ) *
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) =
        -finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) ^ 2) := by
    rw [← hequal]
    exact htotal
  have hden : ((Fintype.card α - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show Fintype.card α - 1 ≠ 0 by omega)
  apply (eq_div_iff hden).2
  simpa [mul_comm] using hmul

private lemma perm_squareMean {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (y : α → ℚ) (i : α) :
    finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) ^ 2) =
      (∑ a, y a ^ 2) / Fintype.card α := by
  simpa using perm_coordinateMean (fun a => y a ^ 2) i

private lemma perm_crossMean {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (y : α → ℚ) (hy : ∑ a, y a = 0)
    (i j : α) (hij : i ≠ j) (hcard : 2 ≤ Fintype.card α) :
    finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) =
      -(∑ a, y a ^ 2) /
        ((Fintype.card α : ℚ) * (Fintype.card α - 1 : ℕ)) := by
  rw [perm_crossMean_of_sum_eq_zero y hy i j hij hcard]
  rw [perm_squareMean]
  ring

/-- Dot product of `x` with a uniformly permuted copy of `y`. -/
private def permutedDot {α : Type*} [Fintype α]
    (x y : α → ℚ) (σ : Equiv.Perm α) : ℚ :=
  ∑ i, x i * y (σ i)

private lemma permutedDot_uniformMean {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (x y : α → ℚ) (hy : ∑ i, y i = 0) :
    finiteUniformMean (permutedDot x y) = 0 := by
  rw [show permutedDot x y =
      (fun σ : Equiv.Perm α => ∑ i, x i * y (σ i)) by rfl]
  rw [finiteUniformMean_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  calc
    finiteUniformMean (fun σ : Equiv.Perm α => x i * y (σ i)) =
        finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * x i) := by
          congr 1
          funext σ
          ring
    _ = finiteUniformMean (fun σ : Equiv.Perm α => y (σ i)) * x i :=
      finiteUniformMean_mul_const _ _
    _ = 0 := by rw [perm_coordinateMean_eq_zero y hy]; simp

private lemma permutedDot_sq_uniformMean {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (x y : α → ℚ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0)
    (hcard : 2 ≤ Fintype.card α) :
    finiteUniformMean (fun σ : Equiv.Perm α => (permutedDot x y σ) ^ 2) =
      (∑ i, x i ^ 2) * (∑ i, y i ^ 2) / (Fintype.card α - 1 : ℕ) := by
  have hN : (Fintype.card α : ℚ) ≠ 0 := by positivity
  have hNm1 : ((Fintype.card α - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show Fintype.card α - 1 ≠ 0 by omega)
  have hNsplit :
      (Fintype.card α : ℚ) = ((Fintype.card α - 1 : ℕ) : ℚ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ Fintype.card α by omega)).symm
  have hscale (i j : α) :
      finiteUniformMean
          (fun σ : Equiv.Perm α => (x i * y (σ i)) * (x j * y (σ j))) =
        x i * x j *
          finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) := by
    calc
      _ = finiteUniformMean
          (fun σ : Equiv.Perm α => (y (σ i) * y (σ j)) * (x i * x j)) := by
            congr 1
            funext σ
            ring
      _ = finiteUniformMean (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) *
          (x i * x j) := finiteUniformMean_mul_const _ _
      _ = _ := by ring
  have hdiag (i : α) :
      finiteUniformMean
          (fun σ : Equiv.Perm α => (x i * y (σ i)) * (x i * y (σ i))) =
        x i ^ 2 * ((∑ a, y a ^ 2) / Fintype.card α) := by
    rw [hscale]
    rw [show (fun σ : Equiv.Perm α => y (σ i) * y (σ i)) =
        (fun σ : Equiv.Perm α => y (σ i) ^ 2) by funext σ; ring]
    rw [perm_squareMean]
    ring
  have hoff (i j : α) (hij : i ≠ j) :
      finiteUniformMean
          (fun σ : Equiv.Perm α => (x i * y (σ i)) * (x j * y (σ j))) =
        x i * x j *
          (-(∑ a, y a ^ 2) /
            ((Fintype.card α : ℚ) * (Fintype.card α - 1 : ℕ))) := by
    rw [hscale, perm_crossMean y hy i j hij hcard]
  have hrow (i : α) :
      (∑ j, finiteUniformMean
          (fun σ : Equiv.Perm α => (x i * y (σ i)) * (x j * y (σ j)))) =
        x i ^ 2 * (∑ a, y a ^ 2) / (Fintype.card α - 1 : ℕ) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => finiteUniformMean
        (fun σ : Equiv.Perm α => (x i * y (σ i)) * (x j * y (σ j))))
      (Finset.mem_univ i)]
    rw [hdiag]
    have herase :
        (∑ j ∈ Finset.univ.erase i, finiteUniformMean
            (fun σ : Equiv.Perm α => (x i * y (σ i)) * (x j * y (σ j)))) =
          ∑ j ∈ Finset.univ.erase i,
            x i * x j *
              (-(∑ a, y a ^ 2) /
                ((Fintype.card α : ℚ) * (Fintype.card α - 1 : ℕ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hoff i j (Finset.mem_erase.mp hj).1.symm
    rw [herase]
    rw [show (∑ j ∈ Finset.univ.erase i,
        x i * x j *
          (-(∑ a, y a ^ 2) /
            ((Fintype.card α : ℚ) * (Fintype.card α - 1 : ℕ)))) =
        x i *
          (-(∑ a, y a ^ 2) /
            ((Fintype.card α : ℚ) * (Fintype.card α - 1 : ℕ))) *
          (∑ j ∈ Finset.univ.erase i, x j) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hx]
    field_simp [hN, hNm1]
    rw [hNsplit]
    ring
  rw [show (fun σ : Equiv.Perm α => (permutedDot x y σ) ^ 2) =
      (fun σ : Equiv.Perm α =>
        ∑ i, ∑ j, (x i * y (σ i)) * (x j * y (σ j))) by
        funext σ
        rw [permutedDot, pow_two, Fintype.sum_mul_sum]]
  rw [finiteUniformMean_sum]
  simp_rw [finiteUniformMean_sum]
  simp_rw [hrow]
  calc
    (∑ i, (x i ^ 2 * ∑ a, y a ^ 2) / (Fintype.card α - 1 : ℕ)) =
        ∑ i, x i ^ 2 *
          ((∑ a, y a ^ 2) / (Fintype.card α - 1 : ℕ)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = (∑ i, x i ^ 2) *
          ((∑ a, y a ^ 2) / (Fintype.card α - 1 : ℕ)) := by
            simpa using (Finset.sum_mul Finset.univ
              (fun i => x i ^ 2)
              ((∑ a, y a ^ 2) / (Fintype.card α - 1 : ℕ))).symm
    _ = _ := by ring

private lemma sum_range_cast_rat (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℚ)) =
      (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma sum_range_sq_cast_rat (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℚ) ^ 2) =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma sum_fin_cast_rat (n : ℕ) :
    (∑ i : Fin n, (i : ℚ)) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [show (∑ i ∈ Finset.range n,
      if h : i < n then ((⟨i, h⟩ : Fin n) : ℚ) else 0) =
      ∑ i ∈ Finset.range n, (i : ℚ) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dif_pos (Finset.mem_range.mp hi)]]
  exact sum_range_cast_rat n

private lemma sum_fin_sq_cast_rat (n : ℕ) :
    (∑ i : Fin n, (i : ℚ) ^ 2) =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [show (∑ i ∈ Finset.range n,
      if h : i < n then ((⟨i, h⟩ : Fin n) : ℚ) ^ 2 else 0) =
      ∑ i ∈ Finset.range n, (i : ℚ) ^ 2 by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dif_pos (Finset.mem_range.mp hi)]]
  exact sum_range_sq_cast_rat n

/-- Zero-based ranks centered at their arithmetic mean `(n - 1) / 2`. -/
private def centeredRank (n : ℕ) (i : Fin n) : ℚ :=
  (i : ℚ) - ((n : ℚ) - 1) / 2

private lemma sum_centeredRank (n : ℕ) : ∑ i : Fin n, centeredRank n i = 0 := by
  rw [show (∑ i : Fin n, centeredRank n i) =
      (∑ i : Fin n, (i : ℚ)) -
        ∑ _i : Fin n, ((n : ℚ) - 1) / 2 by
          simp_rw [centeredRank]
          exact Finset.sum_sub_distrib _ _]
  rw [sum_fin_cast_rat]
  simp
  ring

private lemma sum_sq_centeredRank (n : ℕ) :
    ∑ i : Fin n, centeredRank n i ^ 2 =
      (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 12 := by
  have hterm (i : Fin n) :
      centeredRank n i ^ 2 =
        (i : ℚ) ^ 2 - ((n : ℚ) - 1) * (i : ℚ) +
          (((n : ℚ) - 1) / 2) ^ 2 := by
    simp only [centeredRank]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ i : Fin n, ((n : ℚ) - 1) * (i : ℚ)) =
      ((n : ℚ) - 1) * ∑ i : Fin n, (i : ℚ) by
        simpa using (Finset.mul_sum Finset.univ
          (fun i : Fin n => (i : ℚ)) ((n : ℚ) - 1)).symm]
  rw [sum_fin_sq_cast_rat, sum_fin_cast_rat]
  simp
  ring

private lemma sum_sq_centeredRank_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    (∑ i : Fin n, centeredRank n i ^ 2) ≠ 0 := by
  rw [sum_sq_centeredRank]
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn2 : (n : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  exact div_ne_zero (mul_ne_zero hn0 hn2) (by norm_num)

/-- Correlation of a centered vector with a permuted copy of itself. -/
private def permutationCorrelation {α : Type*} [Fintype α]
    (x : α → ℚ) (σ : Equiv.Perm α) : ℚ :=
  permutedDot x x σ / ∑ i, x i ^ 2

private lemma permutationCorrelation_uniformMean
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (x : α → ℚ) (hx : ∑ i, x i = 0) :
    finiteUniformMean (permutationCorrelation x) = 0 := by
  rw [show permutationCorrelation x =
      (fun σ : Equiv.Perm α =>
        permutedDot x x σ * (∑ i, x i ^ 2)⁻¹) by
          funext σ
          simp only [permutationCorrelation, div_eq_mul_inv]]
  rw [finiteUniformMean_mul_const, permutedDot_uniformMean x x hx]
  simp

private lemma permutationCorrelation_uniformVariance
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (x : α → ℚ) (hx : ∑ i, x i = 0)
    (henergy : (∑ i, x i ^ 2) ≠ 0) (hcard : 2 ≤ Fintype.card α) :
    finiteUniformVariance (permutationCorrelation x) =
      1 / (Fintype.card α - 1 : ℕ) := by
  unfold finiteUniformVariance
  rw [permutationCorrelation_uniformMean x hx]
  simp only [sub_zero]
  rw [show (fun σ : Equiv.Perm α => permutationCorrelation x σ ^ 2) =
      (fun σ : Equiv.Perm α =>
        permutedDot x x σ ^ 2 * ((∑ i, x i ^ 2)⁻¹) ^ 2) by
          funext σ
          simp only [permutationCorrelation, div_eq_mul_inv]
          ring]
  rw [finiteUniformMean_mul_const]
  rw [permutedDot_sq_uniformMean x x hx hx hcard]
  have hNm1 : ((Fintype.card α - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show Fintype.card α - 1 ≠ 0 by omega)
  field_simp [henergy, hNm1]

/-- Spearman's rank correlation for two complete, tie-free rank permutations.
The equivalent squared-rank-difference form is Mack (1994), Appendix G,
equation (G4), p. 157. -/
def spearmanRho (n : ℕ) (r s : Equiv.Perm (Fin n)) : ℚ :=
  (∑ i, centeredRank n (r i) * centeredRank n (s i)) /
    ∑ i, centeredRank n i ^ 2

private lemma spearmanRho_eq_permutationCorrelation (n : ℕ)
    (r s : Equiv.Perm (Fin n)) :
    spearmanRho n r s =
      permutationCorrelation (centeredRank n) (s * r⁻¹) := by
  unfold spearmanRho permutationCorrelation permutedDot
  congr 1
  simpa [Equiv.Perm.mul_apply] using
    (Equiv.sum_comp r
      (fun i => centeredRank n i * centeredRank n ((s * r⁻¹) i)))

/-- Exact mean of Spearman's rho when the second rank vector is uniform over
all permutations. This makes the null model behind Mack (1994), Appendix G,
equation (G4), p. 157, explicit. -/
def spearmanPermutationMean (n : ℕ) (r : Equiv.Perm (Fin n)) : ℚ :=
  finiteUniformMean (fun s : Equiv.Perm (Fin n) => spearmanRho n r s)

/-- Exact variance of Spearman's rho when the second rank vector is uniform over
all permutations. This is the finite null model used for Mack's variance
`1 / (n - 1)`, Appendix G, p. 157. -/
def spearmanPermutationVariance (n : ℕ) (r : Equiv.Perm (Fin n)) : ℚ :=
  finiteUniformVariance (fun s : Equiv.Perm (Fin n) => spearmanRho n r s)

/-- Mack's equation (G4) is the centered-rank correlation formula. -/
theorem spearmanRho_eq_one_sub_six_mul_sum_sq_div {n : ℕ} (hn : 2 ≤ n)
    (r s : Equiv.Perm (Fin n)) :
    spearmanRho n r s =
      1 - 6 * (∑ i, (((r i : Fin n) : ℚ) - ((s i : Fin n) : ℚ)) ^ 2) /
        ((n : ℚ) ^ 3 - (n : ℚ)) := by
  have hsq_r :
      (∑ i, centeredRank n (r i) ^ 2) =
        ∑ i, centeredRank n i ^ 2 := by
    exact Equiv.sum_comp r (fun i => centeredRank n i ^ 2)
  have hsq_s :
      (∑ i, centeredRank n (s i) ^ 2) =
        ∑ i, centeredRank n i ^ 2 := by
    exact Equiv.sum_comp s (fun i => centeredRank n i ^ 2)
  have hcross :
      (∑ i, 2 * centeredRank n (r i) * centeredRank n (s i)) =
        2 * ∑ i, centeredRank n (r i) * centeredRank n (s i) := by
    simpa [mul_assoc] using (Finset.mul_sum Finset.univ
      (fun i => centeredRank n (r i) * centeredRank n (s i)) (2 : ℚ)).symm
  have hdiff :
      (∑ i, (((r i : Fin n) : ℚ) - ((s i : Fin n) : ℚ)) ^ 2) =
        2 * (∑ i, centeredRank n i ^ 2) -
          2 * (∑ i, centeredRank n (r i) * centeredRank n (s i)) := by
    calc
      _ = ∑ i, (centeredRank n (r i) - centeredRank n (s i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [centeredRank]
        ring
      _ = (∑ i, centeredRank n (r i) ^ 2) -
          (∑ i, 2 * centeredRank n (r i) * centeredRank n (s i)) +
          ∑ i, centeredRank n (s i) ^ 2 := by
        simp_rw [sub_sq]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = _ := by rw [hsq_r, hsq_s, hcross]; ring
  have henergy := sum_sq_centeredRank_ne_zero hn
  rw [sum_sq_centeredRank] at henergy
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn2 : (n : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hden : (n : ℚ) ^ 3 - (n : ℚ) ≠ 0 := by
    rw [show (n : ℚ) ^ 3 - (n : ℚ) =
        (n : ℚ) * ((n : ℚ) ^ 2 - 1) by ring]
    exact mul_ne_zero hn0 hn2
  unfold spearmanRho
  rw [hdiff, sum_sq_centeredRank]
  field_simp [henergy, hden]
  ring

private theorem spearmanRho_uniformMean_aux {n : ℕ} (hn : 2 ≤ n)
    (r : Equiv.Perm (Fin n)) :
    finiteUniformMean (fun s : Equiv.Perm (Fin n) => spearmanRho n r s) = 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  simp_rw [spearmanRho_eq_permutationCorrelation]
  rw [finiteUniformMean_perm_mulRight]
  exact permutationCorrelation_uniformMean _ (sum_centeredRank n)

private theorem spearmanRho_uniformVariance_aux {n : ℕ} (hn : 2 ≤ n)
    (r : Equiv.Perm (Fin n)) :
    finiteUniformVariance (fun s : Equiv.Perm (Fin n) => spearmanRho n r s) =
      1 / (n - 1 : ℕ) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  rw [show (fun s : Equiv.Perm (Fin n) => spearmanRho n r s) =
      (fun s : Equiv.Perm (Fin n) =>
        permutationCorrelation (centeredRank n) (s * r⁻¹)) by
          funext s
          exact spearmanRho_eq_permutationCorrelation n r s]
  unfold finiteUniformVariance
  rw [finiteUniformMean_perm_mulRight]
  rw [permutationCorrelation_uniformMean _ (sum_centeredRank n)]
  simp only [sub_zero]
  change finiteUniformMean
      (fun ω : Equiv.Perm (Fin n) =>
        (fun σ => permutationCorrelation (centeredRank n) σ ^ 2) (ω * r⁻¹)) = _
  calc
    _ = finiteUniformMean
        (fun σ : Equiv.Perm (Fin n) =>
          permutationCorrelation (centeredRank n) σ ^ 2) :=
      finiteUniformMean_perm_mulRight _ _
    _ = _ := by
      have hcardFin : 2 ≤ Fintype.card (Fin n) := by simpa using hn
      have hv := permutationCorrelation_uniformVariance
        (centeredRank n) (sum_centeredRank n)
        (sum_sq_centeredRank_ne_zero hn) hcardFin
      unfold finiteUniformVariance at hv
      rw [permutationCorrelation_uniformMean _ (sum_centeredRank n)] at hv
      simpa only [sub_zero, Fintype.card_fin] using hv

/-- Under the exact uniform-permutation null, Spearman's rho has mean zero,
as reported after Mack (1994), equation (G4), p. 157. -/
theorem spearmanPermutationMean_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (r : Equiv.Perm (Fin n)) :
    spearmanPermutationMean n r = 0 := by
  simpa [spearmanPermutationMean] using spearmanRho_uniformMean_aux hn r

/-- Under the exact uniform-permutation null, Spearman's rho has variance
`1 / (n - 1)`, as reported after Mack (1994), equation (G4), p. 157. -/
theorem spearmanPermutationVariance_eq {n : ℕ} (hn : 2 ≤ n)
    (r : Equiv.Perm (Fin n)) :
    spearmanPermutationVariance n r = 1 / (n - 1 : ℕ) := by
  simpa [spearmanPermutationVariance] using spearmanRho_uniformVariance_aux hn r

/-- The exact single-column null targets reported after Mack (1994), equation
(G4), p. 157: mean zero and variance `1 / (q - 1)`. They require an
independent uniform-permutation model for the two untied rank vectors. -/
def mackSpearmanNullMomentTargets (q : ℕ) : ℝ × ℝ :=
  (0, 1 / ((q : ℝ) - 1))

/-- The aggregate null-variance target in Mack (1994), equation (G6), p. 158.
It equals the reciprocal of the sum of the inverse-variance weights only when
the component Spearman statistics are pairwise uncorrelated. -/
def developmentCorrelationNominalVariance (n : ℕ) : ℝ :=
  1 / ∑ k ∈ Ico 1 (n - 2), (((adjacentFactorRows n k).card : ℝ) - 1)

/-- Mack's approximate 50 percent Normal acceptance rule following equation
(G6), p. 159. The constant `67 / 100` is a decimal approximation, so this is
a calibration definition and not a theorem about the null rejection rate. -/
def developmentCorrelationAccepts (C : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  |developmentCorrelationTest C n| ≤
    (67 / 100 : ℝ) * Real.sqrt (developmentCorrelationNominalVariance n)

/-! ## Calendar-year statistic -/

/-- Mack's small, median, and large classes within a development-factor
column, Appendix H, p. 163. For an odd untied column the median is removed.
Mack gives no tie rule; strict ranks make the behavior explicit here. -/
inductive FactorBand
  | small
  | median
  | large
  deriving DecidableEq

/-- Classify one factor by its rank in its full development-factor column,
following Mack (1994), Appendix H, p. 163. -/
def factorBand (C : ℕ → ℕ → ℝ) (n i k : ℕ) : FactorBand :=
  let rows := contributors n k
  let r := factorRankOn C rows k i
  let q := rows.card
  if 2 * r ≤ q then .small else if q + 1 < 2 * r then .large else .median

/-- Accident years on zero-based factor diagonal `j`, corresponding to
`A_{j+1}` in Mack's one-based notation, Appendix H, p. 162. The intended range
is `j < n - 1`; the factor column paired with row `i` is `j - i`. -/
def calendarDiagonalRows (j : ℕ) : Finset ℕ := range (j + 1)

/-- Number of small factors on calendar diagonal `j`, as defined before
Mack (1994), Appendix H, equation (H1), pp. 163-165. -/
def calendarSmallCount (C : ℕ → ℕ → ℝ) (n j : ℕ) : ℕ :=
  ((calendarDiagonalRows j).filter fun i => factorBand C n i (j - i) = .small).card

/-- Number of large factors on calendar diagonal `j`, as defined before
Mack (1994), Appendix H, equation (H1), pp. 163-165. -/
def calendarLargeCount (C : ℕ → ℕ → ℝ) (n j : ℕ) : ℕ :=
  ((calendarDiagonalRows j).filter fun i => factorBand C n i (j - i) = .large).card

/-- Number of nonmedian factors retained on calendar diagonal `j`, Mack
(1994), Appendix H, pp. 163-164. -/
def calendarRetainedCount (C : ℕ → ℕ → ℝ) (n j : ℕ) : ℕ :=
  calendarSmallCount C n j + calendarLargeCount C n j

/-- Calendar-diagonal imbalance score `Z_j = min(L_j, S_j)`, Mack (1994),
Appendix H, p. 164. -/
def calendarYearScore (C : ℕ → ℕ → ℝ) (n j : ℕ) : ℕ :=
  min (calendarLargeCount C n j) (calendarSmallCount C n j)

/-- Mack's aggregate calendar-year statistic `Z = Z_2 + ... + Z_{I-1}`,
Appendix H, p. 165, in zero-based indexing. Diagonals with at most one
retained factor contribute zero automatically. -/
def calendarYearTest (C : ℕ → ℕ → ℝ) (n : ℕ) : ℕ :=
  ∑ j ∈ Ico 1 (n - 1), calendarYearScore C n j

/-! ## Exact fair-sign calculations -/

/-- Probability mass of `l` large labels under the explicit fair-sign null:
`binomial(n, 1/2)`, Mack (1994), Appendix H, p. 164. -/
def fairSignMass (n l : ℕ) : ℝ :=
  (n.choose l : ℝ) / (2 : ℝ) ^ n

/-- The score when `l` of `n` retained labels are large, as in Mack (1994),
Appendix H, p. 164. -/
def balancedLabelCount (n l : ℕ) : ℕ := min l (n - l)

/-- Exact finite mean of the calendar score under the independent fair-label
null used before Mack (1994), equation (H1), pp. 164-165. -/
def calendarNullMean (n : ℕ) : ℝ :=
  ∑ l ∈ range (n + 1), fairSignMass n l * balancedLabelCount n l

/-- Exact finite second moment of the calendar score under the independent
fair-label null used before Mack (1994), equation (H2), pp. 164-165. -/
def calendarNullSecondMoment (n : ℕ) : ℝ :=
  ∑ l ∈ range (n + 1), fairSignMass n l * (balancedLabelCount n l : ℝ) ^ 2

/-- Exact finite variance of the calendar score under the independent
fair-label null used in Mack (1994), equation (H2), p. 165. -/
def calendarNullVariance (n : ℕ) : ℝ :=
  calendarNullSecondMoment n - calendarNullMean n ^ 2

/-- Mack's closed mean formula, Appendix H, equation (H1), p. 165, where
`m = floor((n - 1) / 2)`. -/
def mackCalendarNullMean (n : ℕ) : ℝ :=
  (n : ℝ) / 2 - ((n - 1).choose ((n - 1) / 2) : ℝ) * n / (2 : ℝ) ^ n

/-- Mack's closed variance formula, Appendix H, equation (H2), p. 165, where
`m = floor((n - 1) / 2)`. -/
def mackCalendarNullVariance (n : ℕ) : ℝ :=
  (n : ℝ) * (n - 1) / 4 -
    ((n - 1).choose ((n - 1) / 2) : ℝ) * (n * (n - 1)) / (2 : ℝ) ^ n +
    mackCalendarNullMean n - mackCalendarNullMean n ^ 2

private def signedBinomialTerm (n k : ℕ) : ℤ :=
  ((n : ℤ) - 2 * (k : ℤ)) * (n.choose k : ℤ)

private def absoluteBinomialTerm (n k : ℕ) : ℤ :=
  |(n : ℤ) - 2 * (k : ℤ)| * (n.choose k : ℤ)

private theorem signedBinomialTerm_succ (n k : ℕ) (hk : k + 1 ≤ n) :
    signedBinomialTerm n (k + 1) =
      (n : ℤ) * (((n - 1).choose (k + 1) : ℤ) - ((n - 1).choose k : ℤ)) := by
  have hn : 0 < n := by omega
  have hn_pred : n - 1 + 1 = n := by omega
  have hleftNat :
      n.choose (k + 1) * (n - (k + 1)) = (n - 1).choose (k + 1) * n := by
    simpa [hn_pred, mul_comm] using (Nat.choose_mul_succ_eq (n - 1) (k + 1)).symm
  have hrightNat :
      n.choose (k + 1) * (k + 1) = (n - 1).choose k * n := by
    simpa [hn_pred, mul_comm] using (Nat.add_one_mul_choose_eq (n - 1) k).symm
  have hleft :
      (n.choose (k + 1) : ℤ) * ((n : ℤ) - (k + 1 : ℕ)) =
        ((n - 1).choose (k + 1) : ℤ) * n := by
    exact_mod_cast hleftNat
  have hright :
      (n.choose (k + 1) : ℤ) * (k + 1 : ℕ) =
        ((n - 1).choose k : ℤ) * n := by
    exact_mod_cast hrightNat
  rw [signedBinomialTerm]
  push_cast [Nat.cast_sub hk]
  simp only [Nat.cast_add, Nat.cast_one] at hleft hright ⊢
  linear_combination hleft - hright

private theorem sum_signedBinomialTerm (n r : ℕ) (_hn : 0 < n) (hr : r < n) :
    ∑ k ∈ range (r + 1), signedBinomialTerm n k =
      (n : ℤ) * ((n - 1).choose r : ℤ) := by
  induction r with
  | zero => simp [signedBinomialTerm]
  | succ r ih =>
      rw [sum_range_succ]
      rw [ih (by omega)]
      rw [signedBinomialTerm_succ n r (by omega)]
      ring

private theorem absoluteBinomialTerm_symm (n k : ℕ) (hk : k ≤ n) :
    absoluteBinomialTerm n (n - k) = absoluteBinomialTerm n k := by
  rw [absoluteBinomialTerm, absoluteBinomialTerm]
  rw [Nat.choose_symm hk]
  push_cast [Nat.cast_sub hk]
  congr 1
  rw [show (n : ℤ) - 2 * ((n : ℤ) - k) = -((n : ℤ) - 2 * k) by ring, abs_neg]

private theorem absoluteBinomialTerm_eq_signed (n k : ℕ) (hk : 2 * k ≤ n) :
    absoluteBinomialTerm n k = signedBinomialTerm n k := by
  rw [absoluteBinomialTerm, signedBinomialTerm, abs_of_nonneg]
  omega

private theorem sum_absoluteBinomialTerm_odd (m : ℕ) :
    ∑ k ∈ range (2 * m + 2), absoluteBinomialTerm (2 * m + 1) k =
      2 * (2 * m + 1 : ℤ) * (((2 * m + 1 - 1).choose m : ℕ) : ℤ) := by
  let f := absoluteBinomialTerm (2 * m + 1)
  have hupper :
      ∑ k ∈ range (m + 1), f (m + 1 + k) = ∑ k ∈ range (m + 1), f k := by
    calc
      ∑ k ∈ range (m + 1), f (m + 1 + k) =
          ∑ k ∈ range (m + 1), f (m - k) := by
            apply sum_congr rfl
            intro k hk
            have hk' : k < m + 1 := mem_range.mp hk
            have hs := absoluteBinomialTerm_symm (2 * m + 1) (m + 1 + k) (by omega)
            change f ((2 * m + 1) - (m + 1 + k)) = f (m + 1 + k) at hs
            rw [show (2 * m + 1) - (m + 1 + k) = m - k by omega] at hs
            exact hs.symm
      _ = ∑ k ∈ range (m + 1), f k := by
        simpa [f] using (sum_range_reflect f (m + 1))
  have hlower :
      ∑ k ∈ range (m + 1), f k =
        (2 * m + 1 : ℤ) * (((2 * m + 1 - 1).choose m : ℕ) : ℤ) := by
    calc
      ∑ k ∈ range (m + 1), f k =
          ∑ k ∈ range (m + 1), signedBinomialTerm (2 * m + 1) k := by
            apply sum_congr rfl
            intro k hk
            exact absoluteBinomialTerm_eq_signed _ _ (by have := mem_range.mp hk; omega)
      _ = _ := sum_signedBinomialTerm (2 * m + 1) m (by omega) (by omega)
  rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, sum_range_add, hupper, hlower]
  ring

private theorem sum_absoluteBinomialTerm_even (m : ℕ) :
    ∑ k ∈ range (2 * m + 1), absoluteBinomialTerm (2 * m) k =
      2 * (2 * m : ℤ) * (((2 * m - 1).choose ((2 * m - 1) / 2) : ℕ) : ℤ) := by
  rcases eq_zero_or_pos m with rfl | hm
  · simp [absoluteBinomialTerm]
  let f := absoluteBinomialTerm (2 * m)
  have hcenter : f m = 0 := by simp [f, absoluteBinomialTerm]
  have hupper :
      ∑ k ∈ range m, f (m + 1 + k) = ∑ k ∈ range m, f k := by
    calc
      ∑ k ∈ range m, f (m + 1 + k) = ∑ k ∈ range m, f (m - 1 - k) := by
        apply sum_congr rfl
        intro k hk
        have hk' : k < m := mem_range.mp hk
        have hs := absoluteBinomialTerm_symm (2 * m) (m + 1 + k) (by omega)
        change f (2 * m - (m + 1 + k)) = f (m + 1 + k) at hs
        rw [show 2 * m - (m + 1 + k) = m - 1 - k by omega] at hs
        exact hs.symm
      _ = ∑ k ∈ range m, f k := by
        simpa [f] using (sum_range_reflect f m)
  have hlower :
      ∑ k ∈ range m, f k =
        (2 * m : ℤ) * (((2 * m - 1).choose (m - 1) : ℕ) : ℤ) := by
    calc
      ∑ k ∈ range m, f k =
          ∑ k ∈ range m, signedBinomialTerm (2 * m) k := by
            apply sum_congr rfl
            intro k hk
            exact absoluteBinomialTerm_eq_signed _ _ (by have := mem_range.mp hk; omega)
      _ = _ := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.cast_mul] using
          (sum_signedBinomialTerm (2 * m) (m - 1) (by omega) (by omega))
  have hcenter' : absoluteBinomialTerm (2 * m) m = 0 := by simpa [f] using hcenter
  have hupper' :
      ∑ k ∈ range m, absoluteBinomialTerm (2 * m) (m + 1 + k) =
        ∑ k ∈ range m, absoluteBinomialTerm (2 * m) k := by simpa [f] using hupper
  have hlower' :
      ∑ k ∈ range m, absoluteBinomialTerm (2 * m) k =
        (2 * m : ℤ) * (((2 * m - 1).choose (m - 1) : ℕ) : ℤ) := by simpa [f] using hlower
  rw [show 2 * m + 1 = (m + 1) + m by omega, sum_range_add, sum_range_succ,
    hcenter', add_zero, hupper', hlower']
  have hhalf : (2 * m - 1) / 2 = m - 1 := by omega
  rw [hhalf]
  ring

private theorem sum_absoluteBinomialTerm (n : ℕ) :
    ∑ k ∈ range (n + 1), absoluteBinomialTerm n k =
      2 * (n : ℤ) * (((n - 1).choose ((n - 1) / 2) : ℕ) : ℤ) := by
  rcases n.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul] using sum_absoluteBinomialTerm_even m
  · have hhalf : (2 * m + 1 - 1) / 2 = m := by omega
    simpa [hhalf] using sum_absoluteBinomialTerm_odd m

private theorem two_step_choose_weight (n k : ℕ) :
    (k + 2) * (k + 1) * (n + 2).choose (k + 2) =
      (n + 2) * (n + 1) * n.choose k := by
  have h₁ := Nat.add_one_mul_choose_eq (n + 1) (k + 1)
  have h₂ := Nat.add_one_mul_choose_eq n k
  calc
    (k + 2) * (k + 1) * (n + 2).choose (k + 2) =
        (k + 1) * ((n + 2).choose (k + 2) * (k + 2)) := by ring
    _ = (k + 1) * ((n + 2) * (n + 1).choose (k + 1)) := by rw [← h₁]
    _ = (n + 2) * ((n + 1).choose (k + 1) * (k + 1)) := by ring
    _ = (n + 2) * ((n + 1) * n.choose k) := by rw [← h₂]
    _ = _ := by ring

private theorem sum_falling_mul_choose : ∀ n : ℕ,
    ∑ k ∈ range (n + 1), k * (k - 1) * n.choose k =
      n * (n - 1) * 2 ^ (n - 2)
  | 0 => by simp
  | 1 => by norm_num [sum_range_succ, Nat.choose]
  | n + 2 => by
      rw [sum_range_succ', sum_range_succ']
      simp only [Nat.zero_mul, Nat.mul_zero, add_zero, Nat.add_sub_cancel]
      calc
        ∑ k ∈ range (n + 1),
            (k + 1 + 1) * (k + 1) * (n + 2).choose (k + 1 + 1) =
            ∑ k ∈ range (n + 1), (n + 2) * (n + 1) * n.choose k := by
              apply sum_congr rfl
              intro k _
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                two_step_choose_weight n k
        _ = (n + 2) * (n + 1) * 2 ^ n := by
          rw [← mul_sum, Nat.sum_range_choose]
        _ = (n + 2) * (n + 2 - 1) * 2 ^ (n + 2 - 2) := by
          simp

private def centeredSquareBinomialTerm (n k : ℕ) : ℤ :=
  ((n : ℤ) - 2 * (k : ℤ)) ^ 2 * (n.choose k : ℤ)

private theorem sum_centeredSquareBinomialTerm (n : ℕ) :
    ∑ k ∈ range (n + 1), centeredSquareBinomialTerm n k =
      (n : ℤ) * 2 ^ n := by
  rcases n with _ | _ | n
  · norm_num [centeredSquareBinomialTerm]
  · norm_num [centeredSquareBinomialTerm, sum_range_succ, Nat.choose]
  have hchooseNat := Nat.sum_range_choose (n + 2)
  have hfirstNat := Nat.sum_range_mul_choose (n + 2)
  have hfallingNat := sum_falling_mul_choose (n + 2)
  have hchoose :
      (∑ k ∈ range (n + 2 + 1), ((n + 2).choose k : ℤ)) = (2 : ℤ) ^ (n + 2) := by
    exact_mod_cast hchooseNat
  have hfirst :
      (∑ k ∈ range (n + 2 + 1), (k : ℤ) * ((n + 2).choose k : ℤ)) =
        (n + 2 : ℤ) * 2 ^ (n + 2 - 1) := by
    exact_mod_cast hfirstNat
  have hfalling :
      (∑ k ∈ range (n + 2 + 1),
          (k : ℤ) * ((k - 1 : ℕ) : ℤ) * ((n + 2).choose k : ℤ)) =
        (n + 2 : ℤ) * ((n + 2 - 1 : ℕ) : ℤ) * 2 ^ (n + 2 - 2) := by
    exact_mod_cast hfallingNat
  calc
    ∑ k ∈ range (n + 2 + 1), centeredSquareBinomialTerm (n + 2) k =
        (n + 2 : ℤ) ^ 2 * (∑ k ∈ range (n + 2 + 1), ((n + 2).choose k : ℤ)) -
          4 * (n + 2 : ℤ) *
            (∑ k ∈ range (n + 2 + 1), (k : ℤ) * ((n + 2).choose k : ℤ)) +
          4 * (∑ k ∈ range (n + 2 + 1),
            (k : ℤ) * ((k - 1 : ℕ) : ℤ) * ((n + 2).choose k : ℤ)) +
          4 * (∑ k ∈ range (n + 2 + 1),
            (k : ℤ) * ((n + 2).choose k : ℤ)) := by
            simp only [mul_sum]
            rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
            apply sum_congr rfl
            intro k hk
            have hk' : k ≤ n + 2 := mem_range_succ_iff.mp hk
            by_cases hk0 : k = 0
            · subst k
              norm_num [centeredSquareBinomialTerm]
            rw [centeredSquareBinomialTerm]
            push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0)]
            ring
    _ = (n + 2 : ℤ) * 2 ^ (n + 2) := by
      rw [hchoose, hfirst, hfalling]
      push_cast
      ring_nf

private theorem twice_balancedLabelCount_add_abs (n k : ℕ) (hk : k ≤ n) :
    2 * (balancedLabelCount n k : ℤ) + |(n : ℤ) - 2 * (k : ℤ)| = n := by
  by_cases hleft : 2 * k ≤ n
  · have hmin : k ≤ n - k := by omega
    have hleft' : (2 * k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hleft
    have habs : (0 : ℤ) ≤ (n : ℤ) - 2 * (k : ℤ) := by omega
    rw [balancedLabelCount, min_eq_left hmin, abs_of_nonneg habs]
    ring
  · have hmin : n - k ≤ k := by omega
    have habs : (n : ℤ) - 2 * (k : ℤ) ≤ 0 := by omega
    rw [balancedLabelCount, min_eq_right hmin, abs_of_nonpos habs]
    push_cast [Nat.cast_sub hk]
    ring

private def firstBalancedBinomialNumerator (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (balancedLabelCount n k : ℤ)

private def secondBalancedBinomialNumerator (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (balancedLabelCount n k : ℤ) ^ 2

private theorem firstBalancedBinomialNumerator_identity (n : ℕ) :
    2 * firstBalancedBinomialNumerator n +
        2 * (n : ℤ) * (((n - 1).choose ((n - 1) / 2) : ℕ) : ℤ) =
      (n : ℤ) * 2 ^ n := by
  have hchoose :
      (∑ k ∈ range (n + 1), (n.choose k : ℤ)) = (2 : ℤ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hpointwise :
      2 * firstBalancedBinomialNumerator n +
          (∑ k ∈ range (n + 1), absoluteBinomialTerm n k) =
        (n : ℤ) * (∑ k ∈ range (n + 1), (n.choose k : ℤ)) := by
    rw [firstBalancedBinomialNumerator, mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ n := mem_range_succ_iff.mp hk
    have hbalance := twice_balancedLabelCount_add_abs n k hk'
    rw [absoluteBinomialTerm]
    linear_combination (n.choose k : ℤ) * hbalance
  rw [sum_absoluteBinomialTerm, hchoose] at hpointwise
  exact hpointwise

private theorem secondBalancedBinomialNumerator_identity (n : ℕ) :
    4 * secondBalancedBinomialNumerator n +
        4 * (n : ℤ) ^ 2 * (((n - 1).choose ((n - 1) / 2) : ℕ) : ℤ) =
      (n : ℤ) * (n + 1 : ℕ) * 2 ^ n := by
  have hchoose :
      (∑ k ∈ range (n + 1), (n.choose k : ℤ)) = (2 : ℤ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hpointwise :
      4 * secondBalancedBinomialNumerator n +
          2 * (n : ℤ) * (∑ k ∈ range (n + 1), absoluteBinomialTerm n k) =
        (n : ℤ) ^ 2 * (∑ k ∈ range (n + 1), (n.choose k : ℤ)) +
          ∑ k ∈ range (n + 1), centeredSquareBinomialTerm n k := by
    rw [secondBalancedBinomialNumerator, mul_sum, mul_sum, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ n := mem_range_succ_iff.mp hk
    have hbalance := twice_balancedLabelCount_add_abs n k hk'
    rw [absoluteBinomialTerm, centeredSquareBinomialTerm]
    calc
      4 * ((n.choose k : ℤ) * (balancedLabelCount n k : ℤ) ^ 2) +
          2 * (n : ℤ) *
            (|(n : ℤ) - 2 * (k : ℤ)| * (n.choose k : ℤ)) =
          (n.choose k : ℤ) *
            ((2 * (balancedLabelCount n k : ℤ) + |(n : ℤ) - 2 * (k : ℤ)|) ^ 2 +
              |(n : ℤ) - 2 * (k : ℤ)| ^ 2) := by
                have hs := congrArg
                  (fun x : ℤ =>
                    2 * (n.choose k : ℤ) * |(n : ℤ) - 2 * (k : ℤ)| * x)
                  hbalance
                nlinarith [hs]
      _ = (n : ℤ) ^ 2 * (n.choose k : ℤ) +
          ((n : ℤ) - 2 * (k : ℤ)) ^ 2 * (n.choose k : ℤ) := by
            rw [hbalance, sq_abs]
            ring
  rw [sum_absoluteBinomialTerm, sum_centeredSquareBinomialTerm, hchoose] at hpointwise
  push_cast at hpointwise ⊢
  linear_combination hpointwise

/-- Mack (1994), Appendix H, equation (H1), from the exact finite fair-sign sum. -/
theorem calendarNullMean_eq_mackCalendarNullMean (n : ℕ) :
    calendarNullMean n = mackCalendarNullMean n := by
  have hint := firstBalancedBinomialNumerator_identity n
  have hreal :
      2 * (firstBalancedBinomialNumerator n : ℝ) +
          2 * (n : ℝ) * ((n - 1).choose ((n - 1) / 2) : ℝ) =
        (n : ℝ) * (2 : ℝ) ^ n := by
    exact_mod_cast hint
  have hnum :
      (∑ k ∈ range (n + 1),
          (n.choose k : ℝ) * (balancedLabelCount n k : ℝ)) =
        (firstBalancedBinomialNumerator n : ℝ) := by
    rw [firstBalancedBinomialNumerator]
    push_cast
    rfl
  rw [calendarNullMean, mackCalendarNullMean]
  simp_rw [fairSignMass, div_mul_eq_mul_div]
  rw [← sum_div, hnum]
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  linear_combination hreal

/-- Exact second moment behind Mack's Appendix H equations (H1) and (H2), p. 165. -/
theorem calendarNullSecondMoment_closed (n : ℕ) :
    calendarNullSecondMoment n =
      (n : ℝ) * (n + 1) / 4 -
        ((n - 1).choose ((n - 1) / 2) : ℝ) * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  have hint := secondBalancedBinomialNumerator_identity n
  have hreal :
      4 * (secondBalancedBinomialNumerator n : ℝ) +
          4 * (n : ℝ) ^ 2 * ((n - 1).choose ((n - 1) / 2) : ℝ) =
        (n : ℝ) * (n + 1 : ℕ) * (2 : ℝ) ^ n := by
    exact_mod_cast hint
  have hnum :
      (∑ k ∈ range (n + 1),
          (n.choose k : ℝ) * (balancedLabelCount n k : ℝ) ^ 2) =
        (secondBalancedBinomialNumerator n : ℝ) := by
    rw [secondBalancedBinomialNumerator]
    push_cast
    rfl
  rw [calendarNullSecondMoment]
  simp_rw [fairSignMass, div_mul_eq_mul_div]
  rw [← sum_div, hnum]
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  push_cast at hreal ⊢
  linear_combination hreal

/-- Mack (1994), Appendix H, equation (H2), from the exact finite fair-sign variance. -/
theorem calendarNullVariance_eq_mackCalendarNullVariance (n : ℕ) :
    calendarNullVariance n = mackCalendarNullVariance n := by
  rcases n with _ | n
  · norm_num [calendarNullVariance, calendarNullSecondMoment, calendarNullMean,
      fairSignMass, balancedLabelCount, mackCalendarNullVariance, mackCalendarNullMean]
  rw [calendarNullVariance, calendarNullSecondMoment_closed,
    calendarNullMean_eq_mackCalendarNullMean, mackCalendarNullVariance]
  rw [mackCalendarNullMean]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

/-- Sum of Mack's component means for the calendar-year statistic, following
equation (H2), p. 165. The fair-label null is an extra assumption and is not
implied by median splitting a deterministic triangle. -/
def calendarYearNominalMean (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Ico 1 (n - 1), mackCalendarNullMean (calendarRetainedCount C n j)

/-- Sum of Mack's component variances for the calendar-year statistic,
following equation (H2), pp. 165-166. Mack calls different scores only
"almost" uncorrelated, so this aggregate is a nominal definition. -/
def calendarYearNominalVariance (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Ico 1 (n - 1), mackCalendarNullVariance (calendarRetainedCount C n j)

/-- Mack's approximate 95 percent Normal acceptance rule for the calendar-year
statistic, Appendix H, p. 166. This remains a definition because it uses the
nominal variance sum and an approximate Normal distribution. -/
def calendarYearAccepts (C : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  |(calendarYearTest C n : ℝ) - calendarYearNominalMean C n| ≤
    2 * Real.sqrt (calendarYearNominalVariance C n)

/-- The fair-sign masses sum to one. This is the binomial theorem at one,
the exact combinatorial null used in Mack (1994), Appendix H, p. 164. -/
theorem sum_fairSignMass (n : ℕ) :
    ∑ l ∈ range (n + 1), fairSignMass n l = 1 := by
  simp only [fairSignMass]
  rw [← sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  norm_num

/-- Mack's five-label example has exact mean `50 / 32`, as printed in
Mack (1994), Appendix H, p. 165. -/
theorem calendarNullMean_five : calendarNullMean 5 = 50 / 32 := by
  norm_num [calendarNullMean, fairSignMass, balancedLabelCount, sum_range_succ, Nat.choose]

/-- Mack's five-label example has exact second moment `90 / 32`, as printed
immediately before equation (H1) in Mack (1994), Appendix H, p. 165. -/
theorem calendarNullSecondMoment_five : calendarNullSecondMoment 5 = 90 / 32 := by
  norm_num [calendarNullSecondMoment, fairSignMass, balancedLabelCount, sum_range_succ, Nat.choose]

/-- Mack's five-label example has exact variance `95 / 256`, as printed
immediately before equation (H1) in Mack (1994), Appendix H, p. 165. -/
theorem calendarNullVariance_five : calendarNullVariance 5 = 95 / 256 := by
  rw [calendarNullVariance, calendarNullSecondMoment_five, calendarNullMean_five]
  norm_num

/-- Mack's closed formulas (H1) and (H2) reproduce the exact five-label
enumeration in Mack (1994), Appendix H, p. 165. -/
theorem mackCalendarNullMoments_five :
    mackCalendarNullMean 5 = calendarNullMean 5 ∧
      mackCalendarNullVariance 5 = calendarNullVariance 5 := by
  rw [calendarNullMean_five, calendarNullVariance_five]
  norm_num [mackCalendarNullMean, mackCalendarNullVariance, Nat.choose]

end

end VerifiedReserving
