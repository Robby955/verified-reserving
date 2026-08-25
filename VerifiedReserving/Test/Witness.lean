import VerifiedReserving

/-!
# Non-vacuity witness

The stochastic theorems carry hypotheses ((M1), (M3), (M2'), integrability,
nonvanishing column sums). This file exhibits a concrete `RandomTriangle` on
the one-point probability space that satisfies all of them, and instantiates
the headline theorems on it. It certifies that the hypotheses are jointly
satisfiable, so the theorems are not vacuous. CI runs this file.

The witness is the degenerate triangle `C_{i,k} = 100 · 2^k` with development
factor `f_k = 2` and `σ_k² = 0`: every residual is zero, so (M1), (M3) and
(M2') hold with equality. A witness with genuine randomness is a natural
follow-up; this one already rules out contradictory hypotheses.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving.Witness

noncomputable section

/-- The one-point probability space. -/
abbrev Ω := Unit

def μ : Measure Ω := Measure.dirac ()

instance : IsProbabilityMeasure μ := by
  unfold μ; infer_instance

/-- The degenerate triangle: `C_{i,k} = 100 · 2^k`, with the trivial filtration. -/
def X (n : ℕ) : RandomTriangle Ω n where
  C := fun _ k _ => 100 * (2 : ℝ) ^ k
  D := fun _ => ⊤
  D_le := fun _ => le_top
  D_mono := fun _ _ _ => le_rfl
  meas := fun _ _ _ _ => stronglyMeasurable_const

def f : ℕ → ℝ := fun _ => 2
def σ2 : ℕ → ℝ := fun _ => 0

/-- On a space where everything is measurable, conditional expectation is the
identity almost everywhere. -/
theorem integrable_all (g : Ω → ℝ) : Integrable g μ := by
  unfold μ
  exact integrable_dirac (by simp)

theorem condExp_top (g : Ω → ℝ) : μ[g | (⊤ : MeasurableSpace Ω)] =ᵐ[μ] g := by
  have hconst : g = fun _ => g () := funext fun x => by cases x; rfl
  have hg : StronglyMeasurable[(⊤ : MeasurableSpace Ω)] g := by
    rw [hconst]; exact stronglyMeasurable_const
  exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable le_top hg (integrable_all g))

theorem mack1 (n : ℕ) : Mack1 (X n) μ f := by
  intro i _ k
  refine (condExp_top _).trans (Eventually.of_forall fun ω => ?_)
  simp only [X, f]
  ring

theorem eps_zero (n : ℕ) (i k : ℕ) : (X n).eps f i k = fun _ => 0 := by
  ext ω; simp only [RandomTriangle.eps, X, f]; ring

theorem mack3 (n : ℕ) : Mack3 (X n) μ f σ2 := by
  intro i _ k
  refine (condExp_top _).trans (Eventually.of_forall fun ω => ?_)
  simp [eps_zero, σ2]

theorem mack2' (n : ℕ) : Mack2' (X n) μ f := by
  intro k i _ j _ _
  refine (condExp_top _).trans (Eventually.of_forall fun ω => ?_)
  simp [eps_zero]

theorem Srv_ne_zero (n k : ℕ) (hk : k + 2 ≤ n) : ∀ᵐ ω ∂μ, (X n).Srv k ω ≠ 0 := by
  refine Eventually.of_forall fun ω => ?_
  simp only [RandomTriangle.Srv, S, RandomTriangle.at, X, contributors]
  rw [sum_const, card_range, nsmul_eq_mul]
  have h1 : (0 : ℝ) < ((n - k - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - k - 1 := by omega
    exact_mod_cast this
  positivity

/-- **Instantiated Theorem 2 (first part).** On the witness, `E[f̂_k | D_k] = 2`. -/
theorem fhat_unbiased (n k : ℕ) (hk : k + 2 ≤ n) :
    μ[(X n).fhatRv k | (X n).D k] =ᵐ[μ] fun _ => (2 : ℝ) :=
  condExp_fhatRv (X n) f k (mack1 n) (Srv_ne_zero n k hk) (fun _ _ => integrable_all _)
    (integrable_all _)

/-- **Instantiated Theorem 1.** On the witness the chain-ladder ultimate is a
conditionally unbiased predictor of the true ultimate. -/
theorem ultimate_unbiased (n i : ℕ) (hi : i < n) :
    μ[(X n).ChatRv i i | (X n).D (n - 1 - i)] =ᵐ[μ] μ[(X n).C i (n - 1) | (X n).D (n - 1 - i)] :=
  condExp_ultimate_eq (X n) f i hi (mack1 n) (fun k hk => Srv_ne_zero n k hk)
    (fun _ _ => integrable_all _) (fun _ => integrable_all _) (fun _ => integrable_all _)

end

end VerifiedReserving.Witness
