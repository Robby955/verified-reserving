import VerifiedReserving.TotalReserve

/-!
# The exact conditional MSEP of the total reserve

Mack (1993) states the mean squared error of prediction of the *total* reserve
`R̂ = ∑_i R̂_i` in a Corollary to Theorem 3 and estimates it by `msepTotal`
(`TotalReserve.lean`), a plug-in expression carrying cross terms between
accident years. This file proves the exact object that Corollary approximates.

Write `Ĉ_i = Ĉ_{i,n-1}` for the chain-ladder ultimate of accident year `i`,
`C_i = C_{i,n-1}` for the true ultimate, `D` for the σ-algebra of the observed
data (the one `condMsep_eq` conditions on) and `M_i = E[C_i | D]`. Then

`E[(∑_i Ĉ_i - ∑_i C_i)² | D] = ∑_i (E[C_i² | D] - M_i²) + (∑_i (Ĉ_i - M_i))²`

as soon as the centred true ultimates are conditionally uncorrelated across
accident years, `E[(C_i - M_i)(C_j - M_j) | D] = 0` for `i ≠ j`; that condition
is `CondCrossFree` below and is what independence across accident years
supplies. Under (M1) and (M3) the `i`-th conditional variance is Mack's process
variance (`condVar_C_eq_procVar`) and `M_i = C_{i,n-1-i} ∏ f_k` (Theorem 1), so
the identity reads

`E[(∑_i Ĉ_i - ∑_i C_i)² | D] = ∑_i procVar_i + (∑_i (Ĉ_i - M_i))²`.

The process variances add; the estimation errors add *before* they are squared,
and that is the exact origin of the cross terms in Mack's Corollary. In
particular the total MSEP is at least the sum of the single-year process
variances.

Square integrability is carried as `MemLp _ 2 μ`: on a finite measure it gives
integrability of the variables and, through Hölder, of every product that the
decomposition needs, so no separate list of product-integrability hypotheses is
required.
-/

open MeasureTheory Finset Filter

namespace VerifiedReserving

noncomputable section TotalMsep

variable {Ω : Type*} {D : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
  {ι : Type*} {n : ℕ}

/-! ## The cross-term condition -/

/-- **The cross-term condition across accident years.** For every pair of
distinct indices `i ≠ j` of `s`, the centred targets are conditionally
uncorrelated given `D`:

`E[(Y_i - E[Y_i | D]) (Y_j - E[Y_j | D]) | D] = 0`.

This is what independence across accident years supplies, in the same way that
the `D_k`-conditioned form of (M1) is what it supplies for a single row. Like
`Mack1`, `Mack3` and the `hfut` hypotheses of `condMsep_eq`, it is recorded here
as a hypothesis; the passage from independence of the rows to it is not
formalized. -/
def CondCrossFree (μ : Measure Ω) (D : MeasurableSpace Ω) (s : Finset ι) (Y : ι → Ω → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    μ[fun ω => (Y i ω - (μ[Y i | D]) ω) * (Y j ω - (μ[Y j | D]) ω) | D] =ᵐ[μ] 0

/-! ## Square integrability -/

/-- A square-integrable variable has an integrable square. -/
theorem integrable_sq_of_memLp {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    Integrable (fun ω => (Y ω) ^ 2) μ := by
  refine (hY.integrable_mul hY).congr ?_
  exact Eventually.of_forall fun ω => by simp [Pi.mul_apply, pow_two]

/-! ## The conditional variance as a centred second moment -/

/-- `E[(E[Y | D] - Y)² | D] = E[Y² | D] - E[Y | D]²`: the conditional variance
of `Y` is the conditional second moment of the centred variable. This is
`condExp_sq_sub_of_stronglyMeasurable` with the predictor taken to be `E[Y | D]`
itself. -/
theorem condExp_sq_sub_condExp [IsFiniteMeasure μ] (hD : D ≤ ‹MeasurableSpace Ω›)
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    μ[fun ω => ((μ[Y | D]) ω - Y ω) ^ 2 | D]
      =ᵐ[μ] fun ω => (μ[fun ω => (Y ω) ^ 2 | D]) ω - ((μ[Y | D]) ω) ^ 2 := by
  have hM : MemLp (μ[Y | D]) 2 μ := hY.condExp one_le_two
  have h := condExp_sq_sub_of_stronglyMeasurable hD (μ[Y | D]) Y stronglyMeasurable_condExp
    (hY.integrable one_le_two) (integrable_sq_of_memLp hY) (integrable_sq_of_memLp hM)
    (hM.integrable_mul hY)
  refine h.trans ?_
  filter_upwards with ω
  ring

/-! ## Conditional variances add when the cross terms vanish -/

/-- **The conditional second moment of a sum with vanishing cross terms.** If
`E[Z_i Z_j | D] = 0` for `i ≠ j` in `s`, then
`E[(∑_i Z_i)² | D] = ∑_i E[Z_i² | D]`. Applied to the centred true ultimates
`Z_i = E[C_i | D] - C_i` this is the statement that the conditional variances of
the accident years add. -/
theorem condExp_sq_finsetSum_of_cross [IsFiniteMeasure μ] (s : Finset ι) (Z : ι → Ω → ℝ)
    (hZ : ∀ i ∈ s, MemLp (Z i) 2 μ)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → μ[Z i * Z j | D] =ᵐ[μ] 0) :
    μ[fun ω => (∑ i ∈ s, Z i ω) ^ 2 | D]
      =ᵐ[μ] fun ω => ∑ i ∈ s, (μ[fun ω => (Z i ω) ^ 2 | D]) ω := by
  have hZZ : ∀ i ∈ s, ∀ j ∈ s, Integrable (Z i * Z j) μ :=
    fun i hi j hj => (hZ i hi).integrable_mul (hZ j hj)
  have hrow : ∀ i ∈ s, Integrable (∑ j ∈ s, (Z i * Z j)) μ := by
    intro i hi
    refine (integrable_finsetSum s (fun j hj => hZZ i hi j hj)).congr ?_
    exact Eventually.of_forall fun ω => (Finset.sum_apply ω s _).symm
  have hexp : (fun ω => (∑ i ∈ s, Z i ω) ^ 2) = ∑ i ∈ s, ∑ j ∈ s, (Z i * Z j) := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [pow_two, Finset.sum_mul_sum]
  rw [hexp]
  have h1 := condExp_finsetSum hrow D
  have h2 : ∀ i ∈ s, μ[∑ j ∈ s, (Z i * Z j) | D] =ᵐ[μ] μ[fun ω => (Z i ω) ^ 2 | D] := by
    intro i hi
    have hrowsum := condExp_finsetSum (fun j hj => hZZ i hi j hj) D
    have hzero : ∀ᵐ ω ∂μ, ∀ j ∈ s, j ≠ i → (μ[Z i * Z j | D]) ω = 0 := by
      rw [eventually_all_finset]
      intro j hj
      by_cases hji : j = i
      · exact Eventually.of_forall fun _ hcon => absurd hji hcon
      · filter_upwards [hcross i hi j hj (Ne.symm hji)] with ω hω _
        simpa using hω
    have hdiag : μ[Z i * Z i | D] =ᵐ[μ] μ[fun ω => (Z i ω) ^ 2 | D] := by
      refine condExp_congr_ae ?_
      exact Eventually.of_forall fun ω => by simp [Pi.mul_apply, pow_two]
    refine hrowsum.trans ?_
    filter_upwards [hzero, hdiag] with ω hω hd
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem i hi (fun j hj hji => hω j hj hji)]
    exact hd
  have h3 : ∀ᵐ ω ∂μ, ∀ i ∈ s,
      (μ[∑ j ∈ s, (Z i * Z j) | D]) ω = (μ[fun ω => (Z i ω) ^ 2 | D]) ω := by
    rw [eventually_all_finset]; exact h2
  filter_upwards [h1, h3] with ω hω1 hω3
  rw [hω1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hω3 i hi

/-! ## The exact conditional MSEP of a sum of predictions -/

/-- **Conditional MSEP decomposition for a sum.** For `D`-measurable predictors
`P_i` of square-integrable targets `Y_i` whose centred versions are
conditionally uncorrelated (`CondCrossFree`),

`E[(∑_i P_i - ∑_i Y_i)² | D] = ∑_i (E[Y_i² | D] - E[Y_i | D]²) + (∑_i (P_i - E[Y_i | D]))²`.

The conditional variances add; the estimation errors add before being squared. -/
theorem condExp_sq_finsetSum_sub_of_stronglyMeasurable [IsFiniteMeasure μ]
    (hD : D ≤ ‹MeasurableSpace Ω›) (s : Finset ι) (P Y : ι → Ω → ℝ)
    (hP : ∀ i ∈ s, StronglyMeasurable[D] (P i))
    (hPmem : ∀ i ∈ s, MemLp (P i) 2 μ)
    (hYmem : ∀ i ∈ s, MemLp (Y i) 2 μ)
    (hcross : CondCrossFree μ D s Y) :
    μ[fun ω => (∑ i ∈ s, P i ω - ∑ i ∈ s, Y i ω) ^ 2 | D]
      =ᵐ[μ] fun ω => (∑ i ∈ s, ((μ[fun ω => (Y i ω) ^ 2 | D]) ω - ((μ[Y i | D]) ω) ^ 2))
        + (∑ i ∈ s, (P i ω - (μ[Y i | D]) ω)) ^ 2 := by
  have hPtotSM : StronglyMeasurable[D] (∑ i ∈ s, P i) := Finset.stronglyMeasurable_sum s hP
  have hPtot : MemLp (∑ i ∈ s, P i) 2 μ := memLp_finsetSum' s hPmem
  have hYtot : MemLp (∑ i ∈ s, Y i) 2 μ := memLp_finsetSum' s hYmem
  have hLHS : (fun ω => (∑ i ∈ s, P i ω - ∑ i ∈ s, Y i ω) ^ 2)
      = fun ω => ((∑ i ∈ s, P i) ω - (∑ i ∈ s, Y i) ω) ^ 2 := by
    funext ω; simp [Finset.sum_apply]
  rw [hLHS]
  have hbase := condExp_sq_sub_of_stronglyMeasurable hD (∑ i ∈ s, P i) (∑ i ∈ s, Y i)
    hPtotSM (hYtot.integrable one_le_two) (integrable_sq_of_memLp hYtot)
    (integrable_sq_of_memLp hPtot) (hPtot.integrable_mul hYtot)
  refine hbase.trans ?_
  -- the sum of the conditional expectations
  have hM : μ[∑ i ∈ s, Y i | D] =ᵐ[μ] ∑ i ∈ s, μ[Y i | D] :=
    condExp_finsetSum (fun i hi => (hYmem i hi).integrable one_le_two) D
  -- the conditional variance of the total as a centred second moment
  have hvar := condExp_sq_sub_condExp hD (∑ i ∈ s, Y i) hYtot
  have hcentre : μ[fun ω => ((μ[∑ i ∈ s, Y i | D]) ω - (∑ i ∈ s, Y i) ω) ^ 2 | D]
      =ᵐ[μ] μ[fun ω => (∑ i ∈ s, ((μ[Y i | D]) ω - Y i ω)) ^ 2 | D] := by
    refine condExp_congr_ae ?_
    filter_upwards [hM] with ω hω
    rw [hω, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  -- the cross terms vanish, so the centred second moments add
  have hZmem : ∀ i ∈ s, MemLp (fun ω => (μ[Y i | D]) ω - Y i ω) 2 μ := fun i hi =>
    ((hYmem i hi).condExp one_le_two).sub (hYmem i hi)
  have hZcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      μ[(fun ω => (μ[Y i | D]) ω - Y i ω) * fun ω => (μ[Y j | D]) ω - Y j ω | D] =ᵐ[μ] 0 := by
    intro i hi j hj hij
    refine (condExp_congr_ae ?_).trans (hcross i hi j hj hij)
    refine Eventually.of_forall fun ω => ?_
    simp only [Pi.mul_apply]
    ring
  have hsum := condExp_sq_finsetSum_of_cross (D := D) s
    (fun i ω => (μ[Y i | D]) ω - Y i ω) hZmem hZcross
  have hZsq : ∀ᵐ ω ∂μ, ∀ i ∈ s, (μ[fun ω => ((μ[Y i | D]) ω - Y i ω) ^ 2 | D]) ω
      = (μ[fun ω => (Y i ω) ^ 2 | D]) ω - ((μ[Y i | D]) ω) ^ 2 := by
    rw [eventually_all_finset]
    exact fun i hi => condExp_sq_sub_condExp hD (Y i) (hYmem i hi)
  filter_upwards [hvar, hcentre, hsum, hZsq, hM] with ω h1 h2 h3 h4 h5
  have hfirst : (μ[fun ω => ((∑ i ∈ s, Y i) ω) ^ 2 | D]) ω - ((μ[∑ i ∈ s, Y i | D]) ω) ^ 2
      = ∑ i ∈ s, ((μ[fun ω => (Y i ω) ^ 2 | D]) ω - ((μ[Y i | D]) ω) ^ 2) := by
    rw [← h1, h2, h3]
    exact Finset.sum_congr rfl fun i hi => h4 i hi
  have hsecond : (∑ i ∈ s, P i) ω - (μ[∑ i ∈ s, Y i | D]) ω
      = ∑ i ∈ s, (P i ω - (μ[Y i | D]) ω) := by
    rw [h5, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  rw [hfirst, hsecond]

/-! ## Mack's Corollary in exact form -/

/-- Square integrability passes to the residuals `ε_{i,k} = C_{i,k+1} - f_k C_{i,k}`. -/
theorem memLp_eps (X : RandomTriangle Ω n) (f : ℕ → ℝ) (i k : ℕ)
    (hC : ∀ j, MemLp (X.C i j) 2 μ) : MemLp (X.eps f i k) 2 μ := by
  have h : X.eps f i k = X.C i (k + 1) - (f k) • X.C i k := by
    funext ω; simp [RandomTriangle.eps, smul_eq_mul]
  rw [h]
  exact (hC (k + 1)).sub ((hC k).const_smul (f k))

/-- **Theorem 1 at the ultimate, conditioned on the observed data.** Under (M1),
if `D` carries no extra information about row `i`'s future (`hfut1`), then
`E[C_{i,n-1} | D] = C_{i,n-1-i} ∏_{l=n-1-i}^{n-2} f_l`. -/
theorem condExp_ultimate_of_Mack1 [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f : ℕ → ℝ)
    (i : ℕ) (hi : i < n)
    (hfut1 : μ[X.C i (n - 1) | D] =ᵐ[μ] μ[X.C i (n - 1) | X.D (n - 1 - i)])
    (hM : Mack1 X μ f) (hC : ∀ k, Integrable (X.C i k) μ) :
    μ[X.C i (n - 1) | D]
      =ᵐ[μ] fun ω => X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1), f l := by
  have hidx : n - 1 - i + i = n - 1 := by omega
  have h := condExp_C_of_Mack1 X f i i hi hM hC
  rw [hidx] at h
  exact hfut1.trans h

/-- **The conditional variance of the true ultimate, given the observed data.**
Under (M1) and (M3), and with `D` carrying no extra information about row `i`'s
future, `E[C_{i,n-1}² | D] - E[C_{i,n-1} | D]² = procVar C_{i,n-1-i} f σ² (n-1-i) i`. -/
theorem condVar_ultimate_eq_procVar [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (f σ2 : ℕ → ℝ) (i : ℕ) (hi : i < n)
    (hfut1 : μ[X.C i (n - 1) | D] =ᵐ[μ] μ[X.C i (n - 1) | X.D (n - 1 - i)])
    (hfut2 : μ[fun ω => (X.C i (n - 1) ω) ^ 2 | D]
      =ᵐ[μ] μ[fun ω => (X.C i (n - 1) ω) ^ 2 | X.D (n - 1 - i)])
    (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2)
    (hC : ∀ k, Integrable (X.C i k) μ)
    (hCsq : ∀ k, Integrable (fun ω => (X.C i k ω) ^ 2) μ)
    (hε2 : ∀ k, Integrable (fun ω => (X.eps f i k ω) ^ 2) μ)
    (hCε : ∀ k, Integrable (fun ω => X.C i k ω * X.eps f i k ω) μ) :
    (fun ω => (μ[fun ω => (X.C i (n - 1) ω) ^ 2 | D]) ω - ((μ[X.C i (n - 1) | D]) ω) ^ 2)
      =ᵐ[μ] fun ω => procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) i := by
  have hidx : n - 1 - i + i = n - 1 := by omega
  have h := condVar_C_eq_procVar X f σ2 i i hi hM h3 hC hCsq hε2 hCε
  rw [hidx] at h
  filter_upwards [h, hfut1, hfut2] with ω h1 h2 h3'
  rw [h3', h2]
  exact h1

/-- **Mack's Corollary, exact form.** Let `D` be the σ-algebra of the observed
data, `s` a finite set of accident years, `Ĉ_i = Ĉ_{i,n-1}` the chain-ladder
ultimates and `C_i = C_{i,n-1}` the true ultimates. Assume (M1), (M3), square
integrability of the claims and of the predictions, that `D` carries no extra
information about any single row's future (`hfut1`, `hfut2`, as in
`condMsep_eq`), and that the centred true ultimates are conditionally
uncorrelated across accident years (`CondCrossFree`, what independence across
accident years supplies). Then the conditional mean squared error of prediction
of the total splits exactly into the sum of the single-year process variances
and the square of the summed estimation errors:

`E[(∑_i Ĉ_i - ∑_i C_i)² | D] = ∑_i procVar_i + (∑_i (Ĉ_i - C_{i,n-1-i} ∏ f))²`.

Mack's plug-in `msepTotal` estimates the right-hand side; expanding the square
is where the cross terms `mackCross` of the Corollary come from. -/
theorem condMsepTotal_eq [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f σ2 : ℕ → ℝ)
    (s : Finset ℕ) (hD : D ≤ ‹MeasurableSpace Ω›) (hs : ∀ i ∈ s, i < n)
    (hPmeas : ∀ i ∈ s, StronglyMeasurable[D] (X.ChatRv i i))
    (hPmem : ∀ i ∈ s, MemLp (X.ChatRv i i) 2 μ)
    (hCmem : ∀ i ∈ s, ∀ k, MemLp (X.C i k) 2 μ)
    (hcross : CondCrossFree μ D s fun i => X.C i (n - 1))
    (hfut1 : ∀ i ∈ s, μ[X.C i (n - 1) | D] =ᵐ[μ] μ[X.C i (n - 1) | X.D (n - 1 - i)])
    (hfut2 : ∀ i ∈ s, μ[fun ω => (X.C i (n - 1) ω) ^ 2 | D]
      =ᵐ[μ] μ[fun ω => (X.C i (n - 1) ω) ^ 2 | X.D (n - 1 - i)])
    (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2) :
    μ[fun ω => (∑ i ∈ s, X.ChatRv i i ω - ∑ i ∈ s, X.C i (n - 1) ω) ^ 2 | D]
      =ᵐ[μ] fun ω => (∑ i ∈ s, procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) i)
        + (∑ i ∈ s, (X.ChatRv i i ω
            - X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1), f l)) ^ 2 := by
  have hdec := condExp_sq_finsetSum_sub_of_stronglyMeasurable hD s
    (fun i => X.ChatRv i i) (fun i => X.C i (n - 1)) hPmeas hPmem
    (fun i hi => hCmem i hi (n - 1)) hcross
  refine hdec.trans ?_
  -- the per-year identifications
  have hvar : ∀ᵐ ω ∂μ, ∀ i ∈ s,
      (μ[fun ω => (X.C i (n - 1) ω) ^ 2 | D]) ω - ((μ[X.C i (n - 1) | D]) ω) ^ 2
        = procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) i := by
    rw [eventually_all_finset]
    intro i hi
    exact condVar_ultimate_eq_procVar X f σ2 i (hs i hi) (hfut1 i hi) (hfut2 i hi) hM h3
      (fun k => (hCmem i hi k).integrable one_le_two)
      (fun k => integrable_sq_of_memLp (hCmem i hi k))
      (fun k => integrable_sq_of_memLp (memLp_eps X f i k (hCmem i hi)))
      (fun k => ((hCmem i hi k).integrable_mul (memLp_eps X f i k (hCmem i hi))))
  have hmean : ∀ᵐ ω ∂μ, ∀ i ∈ s, (μ[X.C i (n - 1) | D]) ω
      = X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1), f l := by
    rw [eventually_all_finset]
    intro i hi
    exact condExp_ultimate_of_Mack1 X f i (hs i hi) (hfut1 i hi) hM
      (fun k => (hCmem i hi k).integrable one_le_two)
  filter_upwards [hvar, hmean] with ω h1 h2
  congr 1
  · exact Finset.sum_congr rfl fun i hi => h1 i hi
  · exact congrArg (· ^ 2) (Finset.sum_congr rfl fun i hi => by rw [h2 i hi])

/-- **The exact total MSEP is at least the sum of the process variances.** The
estimation-error part of `condMsepTotal_eq` is a square, so the conditional
MSEP of the total reserve dominates `∑_i procVar_i`, whatever the chain-ladder
predictions happen to be. -/
theorem sum_procVar_le_condMsepTotal [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (f σ2 : ℕ → ℝ) (s : Finset ℕ) (hD : D ≤ ‹MeasurableSpace Ω›) (hs : ∀ i ∈ s, i < n)
    (hPmeas : ∀ i ∈ s, StronglyMeasurable[D] (X.ChatRv i i))
    (hPmem : ∀ i ∈ s, MemLp (X.ChatRv i i) 2 μ)
    (hCmem : ∀ i ∈ s, ∀ k, MemLp (X.C i k) 2 μ)
    (hcross : CondCrossFree μ D s fun i => X.C i (n - 1))
    (hfut1 : ∀ i ∈ s, μ[X.C i (n - 1) | D] =ᵐ[μ] μ[X.C i (n - 1) | X.D (n - 1 - i)])
    (hfut2 : ∀ i ∈ s, μ[fun ω => (X.C i (n - 1) ω) ^ 2 | D]
      =ᵐ[μ] μ[fun ω => (X.C i (n - 1) ω) ^ 2 | X.D (n - 1 - i)])
    (hM : Mack1 X μ f) (h3 : Mack3 X μ f σ2) :
    (fun ω => ∑ i ∈ s, procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) i)
      ≤ᵐ[μ] μ[fun ω => (∑ i ∈ s, X.ChatRv i i ω - ∑ i ∈ s, X.C i (n - 1) ω) ^ 2 | D] := by
  filter_upwards [condMsepTotal_eq X f σ2 s hD hs hPmeas hPmem hCmem hcross hfut1 hfut2 hM h3]
    with ω hω
  rw [hω]
  nlinarith [sq_nonneg (∑ i ∈ s, (X.ChatRv i i ω
    - X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1), f l))]

end TotalMsep

/-! ## The plug-in mirrors the exact decomposition

The exact decomposition is `∑_i procVar_i + (∑_i (Ĉ_i - M_i))²`. Mack's plug-in
`msepTotal` has the same two-part shape: `∑_i mackProcess_i`, the process
variances with `f̂, σ̂²` substituted, plus `mackTotalEstimation`, the estimator of
the squared summed estimation error (single-year terms and cross terms
together). The two parts are separated inside `msep` by the two summands
`1/Ĉ_{i,k}` and `1/S_k` of Mack's formula, and separating them is an identity of
the deterministic layer once the row's development factors and projections do
not vanish, which they do not on any real triangle. -/
section PlugIn

open Finset

/-- **Mack's single-year plug-in splits into process variance and estimation
error.** `msep C n i = mackProcess C n i i + mackEstimation C n i`: the `1/Ĉ_{i,k}`
half of Mack's Theorem 3 formula is exactly `procVar` with `f̂, σ̂²` substituted,
and the `1/S_k` half is exactly `mackEstimation`. -/
theorem msep_eq_mackProcess_add_mackEstimation_of_lt (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i < n)
    (hf : ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0)
    (hChat : ∀ k ∈ Ico (n - 1 - i) (n - 1), Chat C n i k ≠ 0) :
    msep C n i = mackProcess C n i i + mackEstimation C n i := by
  have hdi : n - 1 - i + i = n - 1 := by omega
  have hkey : (ultimate C n i) ^ 2 * ∑ k ∈ Ico (n - 1 - i) (n - 1),
      sigma2 C n k / (fhat C n k) ^ 2 * (1 / Chat C n i k) = mackProcess C n i i := by
    rw [mackProcess, procVar_eq_sum, hdi, Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    have hlen : n - 1 - (n - 1 - i) = i := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j < i := Finset.mem_range.mp hj
    have hlt : n - 1 - i + j < n - 1 := by omega
    have hmem : n - 1 - i + j ∈ Ico (n - 1 - i) (n - 1) := by
      rw [Finset.mem_Ico]; omega
    have hg : fhat C n (n - 1 - i + j) ≠ 0 := hf _ hmem
    have hg2 : (fhat C n (n - 1 - i + j)) ^ 2 ≠ 0 := pow_ne_zero 2 hg
    have hc : Chat C n i (n - 1 - i + j) ≠ 0 := hChat _ hmem
    have hprod : ∏ l ∈ Ico (n - 1 - i) (n - 1), fhat C n l
        = (∏ l ∈ Ico (n - 1 - i) (n - 1 - i + j), fhat C n l)
          * (fhat C n (n - 1 - i + j) * ∏ l ∈ Ico (n - 1 - i + j + 1) (n - 1), fhat C n l) := by
      rw [← Finset.prod_eq_prod_Ico_succ_bot hlt,
        Finset.prod_Ico_consecutive _ (Nat.le_add_right _ _) (le_of_lt hlt)]
    have hU : ultimate C n i
        = C i (n - 1 - i) * ∏ l ∈ Ico (n - 1 - i) (n - 1), fhat C n l := rfl
    have hCh : Chat C n i (n - 1 - i + j)
        = C i (n - 1 - i) * ∏ l ∈ Ico (n - 1 - i) (n - 1 - i + j), fhat C n l := rfl
    rw [hCh] at hc
    rw [hU, hprod, hCh]
    field_simp
  rw [msep, mackEstimation]
  simp only [mul_add]
  rw [Finset.sum_add_distrib, mul_add, hkey]
  congr 1
  exact congrArg _ (Finset.sum_congr rfl fun k _ => mul_one_div _ _)

/-- **Mack's total plug-in has the shape of the exact decomposition.**
`msepTotal C n = ∑_i mackProcess_i + mackTotalEstimation C n`, the plug-in
counterpart of `condMsepTotal_eq`: the process variances add, and everything
else, single-year estimation errors and cross terms alike, is the estimator of
the squared summed estimation error. -/
theorem msepTotal_eq_sum_mackProcess_add_mackTotalEstimation (C : ℕ → ℕ → ℝ) (n : ℕ)
    (hf : ∀ i ∈ range n, ∀ k ∈ Ico (n - 1 - i) (n - 1), fhat C n k ≠ 0)
    (hChat : ∀ i ∈ range n, ∀ k ∈ Ico (n - 1 - i) (n - 1), Chat C n i k ≠ 0) :
    msepTotal C n = ∑ i ∈ range n, mackProcess C n i i + mackTotalEstimation C n := by
  rw [msepTotal, mackTotalEstimation,
    Finset.sum_congr rfl fun i hi => msep_eq_mackProcess_add_mackEstimation_of_lt C n i
      (Finset.mem_range.mp hi) (hf i hi) (hChat i hi),
    Finset.sum_add_distrib]
  ring

end PlugIn

end VerifiedReserving
