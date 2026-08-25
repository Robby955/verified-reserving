import VerifiedReserving.Stochastic

/-!
# Mack (1993), Theorem 1: the chain-ladder ultimate is conditionally unbiased

Under (M1) in the `D_k`-conditioned form, for accident year `i` with latest
observed development year `d = n-1-i`,

* `E[C_{i,d+m} | D_d] = C_{i,d} ∏_{k<d+m} f_k` (iterating (M1) with the
  tower property), and
* `E[C_{i,d} ∏_{k<d+m} f̂_k | D_d] = C_{i,d} ∏_{k<d+m} f_k` (pull out the
  `D_{d+m}`-measurable partial product, apply Theorem 2 to the last factor,
  tower down).

Together: `E[Ĉ_{i,n-1} | D_d] = E[C_{i,n-1} | D_d]`, Mack's Theorem 1, the
statement that the chain-ladder estimator is an unbiased estimator of the
true ultimate claims, given the data.

Products are written as `∏ k ∈ Finset.Ico d (d+m)` so that the statements
match `Chat` in `ChainLadder.lean`.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- The chain-ladder projection of accident year `i` to development year `d+m`,
as a random variable: `C_{i,d} ∏_{k ∈ [d, d+m)} f̂_k`. -/
def RandomTriangle.ChatRv (X : RandomTriangle Ω n) (i m : ℕ) : Ω → ℝ :=
  fun ω => X.C i (n - 1 - i) ω * ∏ k ∈ Ico (n - 1 - i) (n - 1 - i + m), X.fhatRv k ω

theorem RandomTriangle.ChatRv_zero (X : RandomTriangle Ω n) (i : ℕ) :
    X.ChatRv i 0 = X.C i (n - 1 - i) := by
  ext ω; simp [RandomTriangle.ChatRv]

theorem RandomTriangle.ChatRv_succ (X : RandomTriangle Ω n) (i m : ℕ) :
    X.ChatRv i (m + 1) = X.ChatRv i m * X.fhatRv (n - 1 - i + m) := by
  ext ω
  simp only [RandomTriangle.ChatRv, Pi.mul_apply]
  rw [show n - 1 - i + (m + 1) = n - 1 - i + m + 1 from rfl,
    prod_Ico_succ_top (Nat.le_add_right _ _), mul_assoc]

/-- The partial chain-ladder product is `D_{d+m}`-measurable. -/
theorem RandomTriangle.stronglyMeasurable_ChatRv (X : RandomTriangle Ω n) (i m : ℕ) :
    StronglyMeasurable[X.D (n - 1 - i + m)] (X.ChatRv i m) := by
  induction m with
  | zero =>
    rw [X.ChatRv_zero]
    exact X.meas i _ _ le_rfl
  | succ m ih =>
    rw [X.ChatRv_succ]
    refine StronglyMeasurable.mul ?_ ?_
    · exact ih.mono (X.D_mono (Nat.le_succ _))
    · exact X.stronglyMeasurable_fhatRv _ _ le_rfl

/-- Iterating (M1): `E[C_{i,k+1} | D_d] = f_k E[C_{i,k} | D_d]` for `d ≤ k`. -/
theorem condExp_C_succ [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i d k : ℕ)
    (hdk : d ≤ k) (hM : Mack1 X μ f) :
    μ[X.C i (k + 1) | X.D d] =ᵐ[μ] fun ω => f k * (μ[X.C i k | X.D d]) ω := by
  have h1 : μ[X.C i (k + 1) | X.D d] =ᵐ[μ] μ[μ[X.C i (k + 1) | X.D k] | X.D d] :=
    (condExp_condExp_of_le (X.D_mono hdk) (X.D_le k)).symm
  have h2 : μ[μ[X.C i (k + 1) | X.D k] | X.D d] =ᵐ[μ] μ[(f k) • X.C i k | X.D d] := by
    refine condExp_congr_ae ((hM i k).trans ?_)
    exact Eventually.of_forall fun ω => by simp [Pi.smul_apply, smul_eq_mul]
  have h3 : μ[(f k) • X.C i k | X.D d] =ᵐ[μ] (f k) • μ[X.C i k | X.D d] :=
    condExp_smul (f k) (X.C i k) (X.D d)
  refine (h1.trans (h2.trans h3)).trans ?_
  exact Eventually.of_forall fun ω => by simp [Pi.smul_apply, smul_eq_mul]

/-- `E[C_{i,d+m} | D_d] = C_{i,d} ∏_{k ∈ [d,d+m)} f_k` under (M1). -/
theorem condExp_C_of_Mack1 [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i : ℕ) (m : ℕ)
    (hM : Mack1 X μ f)
    (hint : ∀ j, Integrable (X.C i j) μ) :
    μ[X.C i (n - 1 - i + m) | X.D (n - 1 - i)]
      =ᵐ[μ] fun ω => X.C i (n - 1 - i) ω * ∏ k ∈ Ico (n - 1 - i) (n - 1 - i + m), f k := by
  induction m with
  | zero =>
    have hmeas : StronglyMeasurable[X.D (n - 1 - i)] (X.C i (n - 1 - i)) := X.meas i _ _ le_rfl
    refine (condExp_of_stronglyMeasurable (X.D_le _) hmeas (hint _)).symm ▸ ?_
    exact Eventually.of_forall fun ω => by simp
  | succ m ih =>
    have h := condExp_C_succ X f i (n - 1 - i) (n - 1 - i + m) (Nat.le_add_right _ _) hM
    rw [show n - 1 - i + (m + 1) = n - 1 - i + m + 1 from rfl]
    refine h.trans ?_
    filter_upwards [ih] with ω hω
    rw [hω, prod_Ico_succ_top (Nat.le_add_right _ _)]
    ring

/-- **Mack (1993), Theorem 1 (estimator side).** Under (M1),
`E[C_{i,d} ∏_{k ∈ [d,d+m)} f̂_k | D_d] = C_{i,d} ∏_{k ∈ [d,d+m)} f_k`, provided the
partial products are integrable and each column sum along the row is a.s.
nonzero. -/
theorem condExp_ChatRv [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i : ℕ) (m : ℕ)
    (hM : Mack1 X μ f)
    (hS : ∀ k, ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0)
    (hC : ∀ j k, Integrable (X.C j k) μ)
    (hf : ∀ k, Integrable (X.fhatRv k) μ)
    (hprod : ∀ m', Integrable (X.ChatRv i m') μ) :
    μ[X.ChatRv i m | X.D (n - 1 - i)]
      =ᵐ[μ] fun ω => X.C i (n - 1 - i) ω * ∏ k ∈ Ico (n - 1 - i) (n - 1 - i + m), f k := by
  induction m with
  | zero =>
    rw [X.ChatRv_zero]
    have hmeas : StronglyMeasurable[X.D (n - 1 - i)] (X.C i (n - 1 - i)) := X.meas i _ _ le_rfl
    refine (condExp_of_stronglyMeasurable (X.D_le _) hmeas (hC _ _)).symm ▸ ?_
    exact Eventually.of_forall fun ω => by simp
  | succ m ih =>
    set d := n - 1 - i with hd
    set k := d + m with hk
    have hle : X.D d ≤ X.D k := X.D_mono (Nat.le_add_right _ _)
    -- condition on D_k: the partial product comes out, the last factor becomes f_k
    have h1 : μ[X.ChatRv i (m + 1) | X.D k] =ᵐ[μ] X.ChatRv i m * μ[X.fhatRv k | X.D k] := by
      rw [X.ChatRv_succ]
      exact condExp_mul_of_stronglyMeasurable_left (X.stronglyMeasurable_ChatRv i m)
        (by rw [← X.ChatRv_succ]; exact hprod _) (hf k)
    have h2 : X.ChatRv i m * μ[X.fhatRv k | X.D k] =ᵐ[μ] (f k) • X.ChatRv i m := by
      filter_upwards [condExp_fhatRv X f k hM (hS k) (fun j _ => hC j (k + 1)) (hf k)] with ω hω
      simp [Pi.mul_apply, Pi.smul_apply, hω, mul_comm]
    -- tower down to D_d and use the induction hypothesis
    have h3 : μ[X.ChatRv i (m + 1) | X.D d] =ᵐ[μ] μ[μ[X.ChatRv i (m + 1) | X.D k] | X.D d] :=
      (condExp_condExp_of_le hle (X.D_le k)).symm
    have h4 : μ[μ[X.ChatRv i (m + 1) | X.D k] | X.D d] =ᵐ[μ] μ[(f k) • X.ChatRv i m | X.D d] :=
      condExp_congr_ae (h1.trans h2)
    have h5 : μ[(f k) • X.ChatRv i m | X.D d] =ᵐ[μ] (f k) • μ[X.ChatRv i m | X.D d] :=
      condExp_smul (f k) (X.ChatRv i m) (X.D d)
    refine h3.trans (h4.trans (h5.trans ?_))
    filter_upwards [ih] with ω hω
    rw [show d + (m + 1) = k + 1 from rfl, prod_Ico_succ_top (Nat.le_add_right _ _)]
    simp only [Pi.smul_apply, smul_eq_mul, hω]
    ring

/-- **Mack (1993), Theorem 1.** Under (M1), the chain-ladder ultimate
`Ĉ_{i,n-1} = C_{i,d} ∏_{k=d}^{n-2} f̂_k` is a conditionally unbiased estimator of
the true ultimate: `E[Ĉ_{i,n-1} | D_d] = E[C_{i,n-1} | D_d]`, for `i ≤ n-1`. -/
theorem condExp_ultimate_eq [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i : ℕ)
    (hi : i ≤ n - 1) (hM : Mack1 X μ f)
    (hS : ∀ k, ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0)
    (hC : ∀ j k, Integrable (X.C j k) μ)
    (hf : ∀ k, Integrable (X.fhatRv k) μ)
    (hprod : ∀ m', Integrable (X.ChatRv i m') μ) :
    μ[X.ChatRv i i | X.D (n - 1 - i)] =ᵐ[μ] μ[X.C i (n - 1) | X.D (n - 1 - i)] := by
  have hd : n - 1 - i + i = n - 1 := Nat.sub_add_cancel hi
  have h1 := condExp_ChatRv X f i i hM hS hC hf hprod
  have h2 := condExp_C_of_Mack1 X f i i hM (fun j => hC i j)
  rw [hd] at h1 h2
  exact h1.trans h2.symm

end

end VerifiedReserving
