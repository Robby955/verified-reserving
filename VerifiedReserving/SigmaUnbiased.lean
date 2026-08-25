import VerifiedReserving.Variance

/-!
# Unbiasedness of Mack's variance estimator

Mack (1993), proof of Theorem 3: `σ̂_k²` is conditionally unbiased,
`E[σ̂_k² | D_k] = σ_k²`, for `k ≤ n-3`.

Deterministic step: with `ε_i = C_{i,k+1} - f C_{i,k}` and all `C_{i,k} ≠ 0`,

`∑_i C_{i,k}(F_{i,k} - f̂_k)² = ∑_i ε_i² / C_{i,k} - S_k (f̂_k - f)²`.

Stochastic step: take `E[· | D_k]`; `C_{i,k}⁻¹` and `S_k` are `D_k`-measurable,
(M3) gives `σ_k² C_{i,k}` for each `E[ε_i² | D_k]`, and the estimation-variance
theorem gives `σ_k²/S_k` for `E[(f̂_k - f_k)² | D_k]`. The sum has `n-k-1`
terms, so the conditional expectation is `(n-k-1)σ_k² - σ_k² = (n-k-2)σ_k²`,
and dividing by `n-k-2` gives `σ_k²`. This is where the degrees of freedom
in Mack's estimator come from.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

/-! ## Deterministic identity -/

/-- With all contributing `C_{i,k} ≠ 0` and `S_k ≠ 0`, for any `f`:
`∑ C_{i,k}(F_{i,k} - f̂_k)² = ∑ (C_{i,k+1} - f C_{i,k})² / C_{i,k} - S_k (f̂_k - f)²`. -/
theorem weighted_sq_dev_eps (C : ℕ → ℕ → ℝ) (n k : ℕ) (f : ℝ)
    (h : ∀ i ∈ contributors n k, C i k ≠ 0) (hS : S C n k ≠ 0) :
    ∑ i ∈ contributors n k, C i k * (F C i k - fhat C n k) ^ 2
      = (∑ i ∈ contributors n k, (C i (k + 1) - f * C i k) ^ 2 / C i k)
          - S C n k * (fhat C n k - f) ^ 2 := by
  have h1 := weighted_sq_dev C n k (fhat C n k) h
  have h2 := weighted_sq_dev C n k f h
  have hT : T C n k = fhat C n k * S C n k := by
    unfold fhat; field_simp
  have hE : ∑ i ∈ contributors n k, C i k * (F C i k - f) ^ 2
      = ∑ i ∈ contributors n k, (C i (k + 1) - f * C i k) ^ 2 / C i k := by
    refine sum_congr rfl (fun i hi => ?_)
    have := h i hi
    unfold F
    field_simp
  linear_combination h1 - h2 + hE + (2 * (f - fhat C n k)) * hT

/-! ## Stochastic statement -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- Mack's variance estimator as a random variable. -/
def RandomTriangle.sigma2Rv (X : RandomTriangle Ω n) (k : ℕ) : Ω → ℝ :=
  fun ω => sigma2 (X.at ω) n k

/-- The weighted sum of squares around `f̂_k` as a random variable. -/
def RandomTriangle.wssRv (X : RandomTriangle Ω n) (k : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ contributors n k, X.C i k ω * (F (X.at ω) i k - X.fhatRv k ω) ^ 2

theorem RandomTriangle.sigma2Rv_eq (X : RandomTriangle Ω n) (k : ℕ) :
    X.sigma2Rv k = fun ω => (1 / ((n : ℝ) - k - 2)) * X.wssRv k ω := by
  ext ω; rfl

/-- **Conditional expectation of the weighted sum of squares.** Under (M3) and
(M2'), with all contributing `C_{i,k}` and `S_k` a.s. nonzero,
`E[∑ C_{i,k}(F_{i,k} - f̂_k)² | D_k] = (n-k-2) σ_k²`. -/
theorem condExp_wssRv [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (σ2 : ℕ → ℝ)
    (k : ℕ) (hk : k + 2 ≤ n) (h3 : Mack3 X μ f σ2) (h2 : Mack2' X μ f)
    (hC : ∀ i ∈ contributors n k, ∀ᵐ ω ∂μ, X.C i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0)
    (hε : ∀ i j, Integrable (fun ω => X.eps f i k ω * X.eps f j k ω) μ)
    (hεC : ∀ i, Integrable (fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω) μ)
    (hsq : Integrable (fun ω => (X.fhatRv k ω - f k) ^ 2) μ)
    (hSsq : Integrable (fun ω => X.Srv k ω * (X.fhatRv k ω - f k) ^ 2) μ) :
    μ[X.wssRv k | X.D k] =ᵐ[μ] fun _ => ((n : ℝ) - k - 2) * σ2 k := by
  set s := contributors n k with hs
  -- pointwise identity on the good set
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, X.C i k ω ≠ 0 := by
    rw [eventually_all_finset]; exact hC
  set A : Ω → ℝ := fun ω => ∑ i ∈ s, (X.eps f i k ω) ^ 2 / X.C i k ω with hA
  set B : Ω → ℝ := fun ω => X.Srv k ω * (X.fhatRv k ω - f k) ^ 2 with hB
  have hrw : X.wssRv k =ᵐ[μ] A - B := by
    filter_upwards [hall, hS] with ω hω hSω
    simp only [Pi.sub_apply, hA, hB, RandomTriangle.wssRv, RandomTriangle.eps]
    have := weighted_sq_dev_eps (X.at ω) n k (f k) hω hSω
    simpa [RandomTriangle.at, RandomTriangle.fhatRv, RandomTriangle.Srv] using this
  have hAint : Integrable A μ :=
    (integrable_finsetSum s (fun i _ => hεC i)).congr (Eventually.of_forall fun ω => by simp [hA])
  have hBint : Integrable B μ := hSsq
  -- E[A | D_k] = σ² · #s
  have hAcond : μ[A | X.D k] =ᵐ[μ] fun _ => (s.card : ℝ) * σ2 k := by
    have hA' : A = ∑ i ∈ s, fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω := by
      ext ω; simp [hA, Finset.sum_apply]
    rw [hA']
    have hsum := condExp_finsetSum (μ := μ) (m := X.D k) (s := s)
      (f := fun i => fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω) (fun i _ => hεC i)
    refine hsum.trans ?_
    have hterm : ∀ i ∈ s, μ[fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω | X.D k] =ᵐ[μ] fun _ => σ2 k := by
      intro i hi
      -- (ε_i)²/C = C⁻¹ · ε_i² with C⁻¹ D_k-measurable
      have hCmeas : StronglyMeasurable[X.D k] (fun ω => (X.C i k ω)⁻¹) :=
        ((X.meas i k k le_rfl).measurable.inv).stronglyMeasurable
      have heq : (fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω)
          = (fun ω => (X.C i k ω)⁻¹) * fun ω => (X.eps f i k ω) ^ 2 := by
        ext ω; simp [div_eq_inv_mul]
      have hε2 : Integrable (fun ω => (X.eps f i k ω) ^ 2) μ :=
        (hε i i).congr (Eventually.of_forall fun ω => by simp [sq])
      rw [heq]
      refine (condExp_mul_of_stronglyMeasurable_left hCmeas (by rw [← heq]; exact hεC i) hε2).trans ?_
      filter_upwards [h3 i k, hC i hi] with ω hω hCω
      simp only [Pi.mul_apply, hω]
      field_simp
    have hall' : ∀ᵐ ω ∂μ, ∀ i ∈ s,
        (μ[fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω | X.D k]) ω = σ2 k := by
      rw [eventually_all_finset]; exact hterm
    filter_upwards [hall'] with ω hω
    rw [Finset.sum_apply, Finset.sum_congr rfl (fun i hi => hω i hi), Finset.sum_const, nsmul_eq_mul]
  -- E[B | D_k] = σ²
  have hBcond : μ[B | X.D k] =ᵐ[μ] fun _ => σ2 k := by
    have heq : B = X.Srv k * fun ω => (X.fhatRv k ω - f k) ^ 2 := by
      ext ω; simp [hB]
    rw [heq]
    refine (condExp_mul_of_stronglyMeasurable_left (X.stronglyMeasurable_Srv k)
      (by rw [← heq]; exact hBint) hsq).trans ?_
    filter_upwards [condExp_sq_fhatRv_sub X f σ2 k h3 h2 hS hε hsq, hS] with ω hω hSω
    simp only [Pi.mul_apply, hω]
    field_simp
  -- assemble: card s = n - k - 1
  have hcard : (s.card : ℝ) = (n : ℝ) - k - 1 := by
    have h1 : s.card = n - (k + 1) := by
      rw [hs]; unfold contributors; rw [card_range]; omega
    rw [h1, Nat.cast_sub (by omega : k + 1 ≤ n)]
    push_cast
    ring
  have hfinal : μ[X.wssRv k | X.D k] =ᵐ[μ] μ[A | X.D k] - μ[B | X.D k] :=
    (condExp_congr_ae hrw).trans (condExp_sub hAint hBint (X.D k))
  refine hfinal.trans ?_
  filter_upwards [hAcond, hBcond] with ω hω1 hω2
  simp only [Pi.sub_apply, hω1, hω2, hcard]
  ring

/-- **Mack's variance estimator is conditionally unbiased.** Under (M3) and (M2'),
for `k + 3 ≤ n` (at least two contributing accident years), with the stated
integrability and nonvanishing hypotheses, `E[σ̂_k² | D_k] = σ_k²`. -/
theorem condExp_sigma2Rv [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (σ2 : ℕ → ℝ)
    (k : ℕ) (hk : k + 3 ≤ n) (h3 : Mack3 X μ f σ2) (h2 : Mack2' X μ f)
    (hC : ∀ i ∈ contributors n k, ∀ᵐ ω ∂μ, X.C i k ω ≠ 0)
    (hS : ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0)
    (hε : ∀ i j, Integrable (fun ω => X.eps f i k ω * X.eps f j k ω) μ)
    (hεC : ∀ i, Integrable (fun ω => (X.eps f i k ω) ^ 2 / X.C i k ω) μ)
    (hsq : Integrable (fun ω => (X.fhatRv k ω - f k) ^ 2) μ)
    (hSsq : Integrable (fun ω => X.Srv k ω * (X.fhatRv k ω - f k) ^ 2) μ) :
    μ[X.sigma2Rv k | X.D k] =ᵐ[μ] fun _ => σ2 k := by
  have h := condExp_wssRv X f σ2 k (by omega) h3 h2 hC hS hε hεC hsq hSsq
  rw [X.sigma2Rv_eq]
  have hc : (fun ω => (1 / ((n : ℝ) - k - 2)) * X.wssRv k ω)
      = (1 / ((n : ℝ) - k - 2)) • X.wssRv k := by
    ext ω; simp [smul_eq_mul]
  rw [hc]
  refine (condExp_smul _ _ _).trans ?_
  have hk' : (k : ℝ) + 3 ≤ n := by exact_mod_cast hk
  have hne : (n : ℝ) - k - 2 ≠ 0 := by
    have : 0 < (n : ℝ) - k - 2 := by linarith
    exact this.ne'
  filter_upwards [h] with ω hω
  simp only [Pi.smul_apply, smul_eq_mul, hω]
  field_simp

end

end VerifiedReserving
