import VerifiedReserving.Stochastic

/-!
# Conditional variance of the development factor

Mack's remaining assumptions, stated in the `D_k`-conditioned form:

(M3)  `E[(C_{i,k+1} - f_k C_{i,k})² | D_k] = σ_k² C_{i,k}`   (conditional variance), and

(M2') `E[(C_{i,k+1} - f_k C_{i,k})(C_{j,k+1} - f_k C_{j,k}) | D_k] = 0` for `i ≠ j`
      (conditional uncorrelatedness across accident years, which is what
      independence of accident years contributes to the variance calculation).

Main result: on `{S_k ≠ 0}`,

`E[(f̂_k - f_k)² | D_k] = σ_k² / S_k`,

Mack's formula for the estimation variance of a development factor
(Mack 1993, proof of Theorem 3; Mack 1999, s.e.(f̂_k)² = σ̂_k² / S_k).
The argument: `f̂_k - f_k = S_k⁻¹ ∑_i ε_i` with `ε_i = C_{i,k+1} - f_k C_{i,k}`,
expand the square of the sum, the factor `S_k⁻²` comes out, cross terms
vanish by (M2'), diagonal terms give `σ_k² ∑_i C_{i,k} = σ_k² S_k`.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- The one-step residual `ε_{i,k} = C_{i,k+1} - f_k C_{i,k}` as a random variable. -/
def RandomTriangle.eps (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i k : ℕ) : Ω → ℝ :=
  fun ω => X.C i (k + 1) ω - f k * X.C i k ω

/-- Mack's third assumption, `D_k`-conditioned form. -/
def Mack3 (X : RandomTriangle Ω n) (μ : Measure Ω) (f : ℕ → ℝ) (σ2 : ℕ → ℝ) : Prop :=
  ∀ i, i < n → ∀ k, μ[fun ω => (X.eps f i k ω) ^ 2 | X.D k] =ᵐ[μ] fun ω => σ2 k * X.C i k ω

/-- Conditional uncorrelatedness of residuals across accident years (what
independence across accident years contributes). -/
def Mack2' (X : RandomTriangle Ω n) (μ : Measure Ω) (f : ℕ → ℝ) : Prop :=
  ∀ k, ∀ i ∈ contributors n k, ∀ j ∈ contributors n k, i ≠ j →
    μ[fun ω => X.eps f i k ω * X.eps f j k ω | X.D k] =ᵐ[μ] fun _ => 0

/-- `f̂_k - f_k = S_k⁻¹ ∑_i ε_{i,k}` pointwise. -/
theorem RandomTriangle.fhatRv_sub_eq (X : RandomTriangle Ω n) (f : ℕ → ℝ) (k : ℕ) (ω : Ω)
    (hS : X.Srv k ω ≠ 0) :
    X.fhatRv k ω - f k = (X.Srv k ω)⁻¹ * ∑ i ∈ contributors n k, X.eps f i k ω := by
  have hfh : X.fhatRv k ω = (X.Srv k ω)⁻¹ * ∑ i ∈ contributors n k, X.C i (k + 1) ω := by
    rw [X.fhatRv_eq]; simp [Finset.sum_apply]
  have hS' : X.Srv k ω = ∑ i ∈ contributors n k, X.C i k ω := by
    rw [X.Srv_eq_sum]; simp [Finset.sum_apply]
  simp only [RandomTriangle.eps, sum_sub_distrib, ← mul_sum, mul_sub, hfh]
  rw [← hS']
  field_simp

/-- The squared centred factor as an explicit double sum. -/
theorem RandomTriangle.sq_fhatRv_sub (X : RandomTriangle Ω n) (f : ℕ → ℝ) (k : ℕ) (ω : Ω)
    (hS : X.Srv k ω ≠ 0) :
    (X.fhatRv k ω - f k) ^ 2
      = (X.Srv k ω)⁻¹ ^ 2 *
          ∑ i ∈ contributors n k, ∑ j ∈ contributors n k, X.eps f i k ω * X.eps f j k ω := by
  rw [X.fhatRv_sub_eq f k ω hS, mul_pow, sq (∑ i ∈ contributors n k, X.eps f i k ω), sum_mul_sum]

/-- **Estimation variance of the development factor.** Under (M3) and (M2'),
on `{S_k ≠ 0}`, `E[(f̂_k - f_k)² | D_k] = σ_k² / S_k`. -/
theorem condExp_sq_fhatRv_sub [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (σ2 : ℕ → ℝ)
    (k : ℕ) (h3 : Mack3 X μ f σ2) (h2 : Mack2' X μ f)
    (hS : ∀ᵐ ω ∂μ, X.Srv k ω ≠ 0)
    (hε : ∀ i j, Integrable (fun ω => X.eps f i k ω * X.eps f j k ω) μ)
    (hint : Integrable (fun ω => (X.fhatRv k ω - f k) ^ 2) μ) :
    μ[fun ω => (X.fhatRv k ω - f k) ^ 2 | X.D k] =ᵐ[μ] fun ω => σ2 k / X.Srv k ω := by
  set s := contributors n k
  set Q : Ω → ℝ := fun ω => ∑ i ∈ s, ∑ j ∈ s, X.eps f i k ω * X.eps f j k ω with hQ
  set W : Ω → ℝ := fun ω => (X.Srv k ω)⁻¹ ^ 2 with hW
  -- rewrite the integrand as W * Q almost everywhere
  have hrw : (fun ω => (X.fhatRv k ω - f k) ^ 2) =ᵐ[μ] W * Q := by
    filter_upwards [hS] with ω hSω
    simp only [Pi.mul_apply, hW, hQ]
    exact X.sq_fhatRv_sub f k ω hSω
  have hWmeas : StronglyMeasurable[X.D k] W :=
    (((X.stronglyMeasurable_Srv k).measurable.inv).pow_const 2).stronglyMeasurable
  have hinner_int : ∀ i, Integrable (∑ j ∈ s, fun ω => X.eps f i k ω * X.eps f j k ω) μ :=
    fun i => (integrable_finsetSum s (fun j _ => hε i j)).congr
      (Eventually.of_forall fun ω => by simp [Finset.sum_apply])
  have hQint : Integrable Q μ := by
    have := integrable_finsetSum s (fun i _ => hinner_int i)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp [hQ, Finset.sum_apply]
  have hWQint : Integrable (W * Q) μ := hint.congr hrw
  -- pull out W, then evaluate E[Q | D_k] termwise
  have h1 : μ[fun ω => (X.fhatRv k ω - f k) ^ 2 | X.D k] =ᵐ[μ] W * μ[Q | X.D k] :=
    (condExp_congr_ae hrw).trans (condExp_mul_of_stronglyMeasurable_left hWmeas hWQint hQint)
  have hQ' : Q = ∑ i ∈ s, ∑ j ∈ s, fun ω => X.eps f i k ω * X.eps f j k ω := by
    ext ω; simp [hQ, Finset.sum_apply]
  have h2' : μ[Q | X.D k] =ᵐ[μ] fun ω => σ2 k * X.Srv k ω := by
    rw [hQ']
    have hsum := condExp_finsetSum (μ := μ) (m := X.D k) (s := s)
      (f := fun i => ∑ j ∈ s, fun ω => X.eps f i k ω * X.eps f j k ω)
      (fun i _ => hinner_int i)
    refine hsum.trans ?_
    have hinner : ∀ i ∈ s, μ[∑ j ∈ s, fun ω => X.eps f i k ω * X.eps f j k ω | X.D k]
        =ᵐ[μ] fun ω => σ2 k * X.C i k ω := by
      intro i hi
      have hs := condExp_finsetSum (μ := μ) (m := X.D k) (s := s)
        (f := fun j => fun ω => X.eps f i k ω * X.eps f j k ω) (fun j _ => hε i j)
      refine hs.trans ?_
      have hterm : ∀ j ∈ s, μ[fun ω => X.eps f i k ω * X.eps f j k ω | X.D k]
          =ᵐ[μ] fun ω => if j = i then σ2 k * X.C i k ω else 0 := by
        intro j hj
        by_cases hij : j = i
        · subst hij
          have e1 : (fun ω => X.eps f j k ω * X.eps f j k ω) = fun ω => (X.eps f j k ω) ^ 2 := by
            ext ω; ring
          rw [e1]
          exact (h3 j (lt_of_mem_contributors hi) k).trans (Eventually.of_forall fun ω => by simp)
        · exact (h2 k i hi j hj (Ne.symm hij)).trans (Eventually.of_forall fun ω => by simp [hij])
      have hall : ∀ᵐ ω ∂μ, ∀ j ∈ s,
          (μ[fun ω => X.eps f i k ω * X.eps f j k ω | X.D k]) ω
            = if j = i then σ2 k * X.C i k ω else 0 := by
        rw [eventually_all_finset]; exact hterm
      filter_upwards [hall] with ω hω
      rw [Finset.sum_apply, Finset.sum_congr rfl (fun j hj => hω j hj), Finset.sum_ite_eq' s i]
      simp [hi]
    have hall' : ∀ᵐ ω ∂μ, ∀ i ∈ s,
        (μ[∑ j ∈ s, fun ω => X.eps f i k ω * X.eps f j k ω | X.D k]) ω = σ2 k * X.C i k ω := by
      rw [eventually_all_finset]; exact hinner
    filter_upwards [hall'] with ω hω
    rw [Finset.sum_apply, Finset.sum_congr rfl (fun i hi => hω i hi), ← Finset.mul_sum,
      X.Srv_eq_sum, Finset.sum_apply]
  refine h1.trans ?_
  filter_upwards [h2', hS] with ω hω hSω
  simp only [Pi.mul_apply, hω, hW]
  field_simp

end

end VerifiedReserving
