import VerifiedReserving.Variance
import VerifiedReserving.Ultimate

/-!
# Conditional second moments and the process variance along a row

Under (M1) and (M3) in the `D_k`-conditioned form, the residual
`ε_{i,k} = C_{i,k+1} - f_k C_{i,k}` has `E[ε | D_k] = 0` and
`E[ε² | D_k] = σ_k² C_{i,k}`. Expanding `C_{i,k+1} = f_k C_{i,k} + ε` gives the
conditional second moment

`E[C_{i,k+1}² | D_k] = f_k² C_{i,k}² + σ_k² C_{i,k}`.

Iterating with the tower property down to `D_d` (`d ≤ k`) gives the recursion
for the conditional variance `V_d(C_{i,k+1}) = E[C_{i,k+1}² | D_d] - E[C_{i,k+1} | D_d]²`:

`V_d(C_{i,k+1}) = f_k² V_d(C_{i,k}) + σ_k² E[C_{i,k} | D_d]`,

which is the law of total variance specialised to Mack's model, and whose
closed form is the process-variance term of Mack's Theorem 3.

This file proves the one-step second-moment identity and the recursion; the
closed form by induction follows in `Msep.lean`.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- (M1) says the residual has conditional mean zero. -/
theorem condExp_eps [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i k : ℕ)
    (hM : Mack1 X μ f) (hC1 : Integrable (X.C i (k + 1)) μ) (hC0 : Integrable (X.C i k) μ) :
    μ[X.eps f i k | X.D k] =ᵐ[μ] fun _ => 0 := by
  have heq : X.eps f i k = X.C i (k + 1) - (f k) • X.C i k := by
    ext ω; simp [RandomTriangle.eps, smul_eq_mul]
  rw [heq]
  refine (condExp_sub hC1 (hC0.smul (f k)) (X.D k)).trans ?_
  have h1 := hM i k
  have h2 : μ[(f k) • X.C i k | X.D k] =ᵐ[μ] (f k) • μ[X.C i k | X.D k] :=
    condExp_smul (f k) (X.C i k) (X.D k)
  have h3 : μ[X.C i k | X.D k] =ᵐ[μ] X.C i k := by
    refine (condExp_of_stronglyMeasurable (X.D_le k) (X.meas i k k le_rfl) hC0).symm ▸ ?_
    exact Eventually.of_forall fun ω => rfl
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  simp [Pi.sub_apply, hω1, hω2, hω3, smul_eq_mul]

/-- **Conditional second moment.** Under (M1) and (M3),
`E[C_{i,k+1}² | D_k] = f_k² C_{i,k}² + σ_k² C_{i,k}`. -/
theorem condExp_sq_C_succ [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (σ2 : ℕ → ℝ)
    (i k : ℕ) (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hC1 : Integrable (X.C i (k + 1)) μ) (hC0 : Integrable (X.C i k) μ)
    (hε2 : Integrable (fun ω => (X.eps f i k ω) ^ 2) μ)
    (hCε : Integrable (fun ω => X.C i k ω * X.eps f i k ω) μ)
    (hC0sq : Integrable (fun ω => (X.C i k ω) ^ 2) μ) :
    μ[fun ω => (X.C i (k + 1) ω) ^ 2 | X.D k]
      =ᵐ[μ] fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2 + σ2 k * X.C i k ω := by
  -- C_{k+1}² = f² C² + 2 f (C ε) + ε²
  have hexp : (fun ω => (X.C i (k + 1) ω) ^ 2)
      = (fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2) + ((2 * f k) • fun ω => X.C i k ω * X.eps f i k ω)
        + fun ω => (X.eps f i k ω) ^ 2 := by
    ext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RandomTriangle.eps]; ring
  rw [hexp]
  have hA : Integrable (fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2) μ := hC0sq.const_mul _
  have hB : Integrable ((2 * f k) • fun ω => X.C i k ω * X.eps f i k ω) μ := hCε.smul _
  refine (condExp_add (hA.add hB) hε2 (X.D k)).trans ?_
  have hAB := condExp_add hA hB (X.D k)
  -- the D_k-measurable square is its own conditional expectation
  have hA' : μ[fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2 | X.D k] =ᵐ[μ] fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2 := by
    refine (condExp_of_stronglyMeasurable (X.D_le k)
      ((((X.meas i k k le_rfl).measurable.pow_const 2).const_mul _).stronglyMeasurable) hA).symm ▸ ?_
    exact Eventually.of_forall fun ω => rfl
  -- the cross term: C_{i,k} comes out, E[ε | D_k] = 0
  have hB' : μ[(2 * f k) • fun ω => X.C i k ω * X.eps f i k ω | X.D k] =ᵐ[μ] fun _ => 0 := by
    refine (condExp_smul _ _ _).trans ?_
    have hε0 := condExp_eps X f i k hM hC1 hC0
    have hεint : Integrable (X.eps f i k) μ := hC1.sub (hC0.const_mul _)
    have hmul : μ[fun ω => X.C i k ω * X.eps f i k ω | X.D k] =ᵐ[μ] X.C i k * μ[X.eps f i k | X.D k] :=
      condExp_mul_of_stronglyMeasurable_left (X.meas i k k le_rfl) hCε hεint
    filter_upwards [hmul, hε0] with ω hω1 hω2
    simp [Pi.smul_apply, hω1, Pi.mul_apply, hω2]
  filter_upwards [hAB, hA', hB', h3 i k] with ω h1 h2 h3' h4
  simp only [Pi.add_apply, h1, h2, h3', h4]
  ring

/-- Iterated (M1) for the tower step used below: `E[C_{i,k+1} | D_d] = f_k E[C_{i,k} | D_d]`. -/
theorem condExp_C_succ' [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i d k : ℕ)
    (hdk : d ≤ k) (hM : Mack1 X μ f) :
    μ[X.C i (k + 1) | X.D d] =ᵐ[μ] fun ω => f k * (μ[X.C i k | X.D d]) ω :=
  condExp_C_succ X f i d k hdk hM

/-- **Second-moment recursion down to `D_d`.** For `d ≤ k`, under (M1) and (M3),
`E[C_{i,k+1}² | D_d] = f_k² E[C_{i,k}² | D_d] + σ_k² E[C_{i,k} | D_d]`. -/
theorem condExp_sq_C_succ_tower [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ)
    (σ2 : ℕ → ℝ) (i d k : ℕ) (hdk : d ≤ k) (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hC1 : Integrable (X.C i (k + 1)) μ) (hC0 : Integrable (X.C i k) μ)
    (hε2 : Integrable (fun ω => (X.eps f i k ω) ^ 2) μ)
    (hCε : Integrable (fun ω => X.C i k ω * X.eps f i k ω) μ)
    (hC0sq : Integrable (fun ω => (X.C i k ω) ^ 2) μ) :
    μ[fun ω => (X.C i (k + 1) ω) ^ 2 | X.D d]
      =ᵐ[μ] fun ω => (f k) ^ 2 * (μ[fun ω => (X.C i k ω) ^ 2 | X.D d]) ω
                      + σ2 k * (μ[X.C i k | X.D d]) ω := by
  have hle : X.D d ≤ X.D k := X.D_mono hdk
  have h1 : μ[fun ω => (X.C i (k + 1) ω) ^ 2 | X.D d]
      =ᵐ[μ] μ[μ[fun ω => (X.C i (k + 1) ω) ^ 2 | X.D k] | X.D d] :=
    (condExp_condExp_of_le hle (X.D_le k)).symm
  have h2 : μ[μ[fun ω => (X.C i (k + 1) ω) ^ 2 | X.D k] | X.D d]
      =ᵐ[μ] μ[(fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2) + (σ2 k) • X.C i k | X.D d] := by
    refine condExp_congr_ae ((condExp_sq_C_succ X f σ2 i k hM h3 hC1 hC0 hε2 hCε hC0sq).trans ?_)
    exact Eventually.of_forall fun ω => by simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hA : Integrable (fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2) μ := hC0sq.const_mul _
  have h3' := condExp_add hA (hC0.smul (σ2 k)) (X.D d)
  have h4 : μ[fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2 | X.D d]
      =ᵐ[μ] (f k ^ 2) • μ[fun ω => (X.C i k ω) ^ 2 | X.D d] := by
    have : (fun ω => (f k) ^ 2 * (X.C i k ω) ^ 2) = (f k ^ 2) • fun ω => (X.C i k ω) ^ 2 := by
      ext ω; simp [smul_eq_mul]
    rw [this]; exact condExp_smul _ _ _
  have h5 : μ[(σ2 k) • X.C i k | X.D d] =ᵐ[μ] (σ2 k) • μ[X.C i k | X.D d] := condExp_smul _ _ _
  refine h1.trans (h2.trans (h3'.trans ?_))
  filter_upwards [h4, h5] with ω hω4 hω5
  simp [Pi.add_apply, hω4, hω5, Pi.smul_apply, smul_eq_mul]

end

end VerifiedReserving
