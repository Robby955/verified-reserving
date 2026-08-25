import VerifiedReserving.Independence
import VerifiedReserving.TotalMsep

/-!
# The observed-data σ-algebra, and the last hypotheses of Theorem 3 discharged

`Msep.lean` proves Mack's Theorem 3 in exact form conditioned on a σ-algebra
`D` of observed data, under two named hypotheses (`hfut1`, `hfut2`): that `D`
says nothing about accident year `i` beyond that year's own history up to its
latest observed diagonal. `TotalMsep.lean` proves the Corollary for the total
reserve under a third named hypothesis, `CondCrossFree`: the centred true
ultimates of two different accident years are conditionally uncorrelated.
Mack (1993) obtains all three from his assumption (M2), independence across
accident years, in the sentence "Because of the independence of the accident
years" in the proof of Theorem 3 (pp. 217-219).

This file names the σ-algebra Mack conditions on and proves that sentence.
The observed data at the end of development year `n-1` is one diagonal per
accident year: row `i` is observed up to development year `n-1-i`. So

`obsSigma = ⨆_{i < n} rowSigma i (n-1-i)`,

the join of the rows' observed histories. It splits as row `i`'s own observed
history joined with the other rows' (`obsSigma_eq_sup`, the analogue of
`D_eq_sup`), and the other rows are independent of the whole of row `i`, so
`condExp_sup_of_indep` gives

`E[g | obsSigma] = E[g | rowSigma i (n-1-i)]`

for every integrable `g` carried by row `i` (`condExp_obsSigma_eq_rowSigma`).
The same lemma applied to `D_{n-1-i}` gives the same right-hand side, so the
two conditional expectations agree: that is `hfut1` and `hfut2` exactly, and
`condMsep_eq_of_rows` is Theorem 3 with no hypothesis left except Mack's own
row-conditioned assumptions, independence, and integrability.

The cross-term condition is the same argument run on a pair of rows, as in
`mack2'_of_rows`: condition on the observed data together with the whole of
row `j`, pull row `j`'s centred ultimate out of the conditional expectation,
and what remains is row `i`'s centred ultimate conditioned on a σ-algebra that
adds nothing about row `i`, hence zero. The tower property brings the identity
back down to the observed data (`condCrossFree_of_rows`), and
`condMsepTotal_eq_of_rows` is Mack's Corollary in exact form with the same
short hypothesis list.

The chain-ladder estimators are functions of the observed cells only, so they
are `obsSigma`-measurable with no hypothesis
(`stronglyMeasurable_obsSigma_ChatRv`); that discharges `hPmeas` as well.
-/

open MeasureTheory Finset Filter ProbabilityTheory

namespace VerifiedReserving

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-! ## The observed-data σ-algebra -/

/-- **The observed data.** The join over accident years `i < n` of that year's
own history up to its latest observed development year `n-1-i`: the run-off
triangle as it stands after `n` calendar years, which is what Mack (1993)
conditions on in Theorem 3. -/
@[implicit_reducible]
def RandomTriangle.obsSigma (X : RandomTriangle Ω n) : MeasurableSpace Ω :=
  ⨆ i, ⨆ _ : i < n, X.rowSigma i (n - 1 - i)

/-- The observed histories of the accident years other than `i`. -/
@[implicit_reducible]
def RandomTriangle.otherObs (X : RandomTriangle Ω n) (i : ℕ) : MeasurableSpace Ω :=
  ⨆ i', ⨆ _ : i' ≠ i, ⨆ _ : i' < n, X.rowSigma i' (n - 1 - i')

theorem RandomTriangle.rowSigma_le_obsSigma (X : RandomTriangle Ω n) {i : ℕ} (hi : i < n) :
    X.rowSigma i (n - 1 - i) ≤ X.obsSigma :=
  le_iSup₂_of_le (f := fun i (_ : i < n) => X.rowSigma i (n - 1 - i)) i hi le_rfl

theorem RandomTriangle.rowSigma_le_otherObs (X : RandomTriangle Ω n) {i i' : ℕ}
    (hne : i' ≠ i) (hi' : i' < n) : X.rowSigma i' (n - 1 - i') ≤ X.otherObs i :=
  le_iSup₂_of_le (f := fun i' (_ : i' ≠ i) => ⨆ _ : i' < n, X.rowSigma i' (n - 1 - i')) i' hne
    (le_iSup_of_le hi' le_rfl)

theorem RandomTriangle.obsSigma_le (X : RandomTriangle Ω n) :
    X.obsSigma ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun i => iSup_le fun _ => X.rowSigma_le i _

theorem RandomTriangle.otherObs_le_otherRowsAll (X : RandomTriangle Ω n) (i : ℕ) :
    X.otherObs i ≤ X.otherRowsAll i :=
  iSup_le fun i' => iSup_le fun hne => iSup_le fun _ =>
    (X.rowSigma_le_rowSigmaAll i' _).trans (X.rowSigmaAll_le_otherRowsAll hne)

theorem RandomTriangle.otherObs_le (X : RandomTriangle Ω n) (i : ℕ) :
    X.otherObs i ≤ ‹MeasurableSpace Ω› :=
  (X.otherObs_le_otherRowsAll i).trans (X.otherRowsAll_le i)

/-- **The observed data splits at accident year `i`**: row `i`'s own observed
history joined with the other rows'. This is the analogue for the latest
diagonal of `RandomTriangle.D_eq_sup`, and it is what makes Mack's appeal to
independence across accident years available in Theorem 3. -/
theorem RandomTriangle.obsSigma_eq_sup (X : RandomTriangle Ω n) {i : ℕ} (hi : i < n) :
    X.obsSigma = X.rowSigma i (n - 1 - i) ⊔ X.otherObs i := by
  refine le_antisymm ?_ (sup_le (X.rowSigma_le_obsSigma hi) ?_)
  · refine iSup_le fun i' => iSup_le fun hi' => ?_
    by_cases h : i' = i
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (X.rowSigma_le_otherObs h hi')
  · exact iSup_le fun i' => iSup_le fun _ => iSup_le fun hi' => X.rowSigma_le_obsSigma hi'

/-! ## The chain-ladder estimators are functions of the observed data -/

/-- An entry of row `i` observed on or before the latest diagonal is measurable
for the observed data. -/
theorem RandomTriangle.stronglyMeasurable_obsSigma_C (X : RandomTriangle Ω n) {i j : ℕ}
    (hi : i < n) (hj : j ≤ n - 1 - i) : StronglyMeasurable[X.obsSigma] (X.C i j) :=
  (X.stronglyMeasurable_rowSigma i hj).mono (X.rowSigma_le_obsSigma hi)

/-- The column sum `S_k` uses only observed cells. -/
theorem RandomTriangle.stronglyMeasurable_obsSigma_Srv (X : RandomTriangle Ω n) (k : ℕ) :
    StronglyMeasurable[X.obsSigma] (X.Srv k) := by
  rw [X.Srv_eq_sum]
  refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
  have h : i < n - k - 1 := by simpa [contributors] using hi
  exact X.stronglyMeasurable_obsSigma_C (by omega) (by omega)

/-- **The development factor is a function of the observed data.** Every cell
entering `f̂_k` is observed: `i` contributes only when `C_{i,k+1}` is on or
above the latest diagonal. -/
theorem RandomTriangle.stronglyMeasurable_obsSigma_fhatRv (X : RandomTriangle Ω n) (k : ℕ) :
    StronglyMeasurable[X.obsSigma] (X.fhatRv k) := by
  rw [X.fhatRv_eq]
  refine StronglyMeasurable.mul ?_ ?_
  · exact ((X.stronglyMeasurable_obsSigma_Srv k).measurable.inv).stronglyMeasurable
  · refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    have h : i < n - k - 1 := by simpa [contributors] using hi
    exact X.stronglyMeasurable_obsSigma_C (by omega) (by omega)

/-- **The chain-ladder prediction is a function of the observed data**, which
is the hypothesis `hPmeas` of `condMsep_eq`. -/
theorem RandomTriangle.stronglyMeasurable_obsSigma_ChatRv (X : RandomTriangle Ω n) {i : ℕ}
    (hi : i < n) (m : ℕ) : StronglyMeasurable[X.obsSigma] (X.ChatRv i m) := by
  induction m with
  | zero =>
    rw [X.ChatRv_zero]
    exact X.stronglyMeasurable_obsSigma_C hi le_rfl
  | succ m ih =>
    rw [X.ChatRv_succ]
    exact ih.mul (X.stronglyMeasurable_obsSigma_fhatRv _)

/-! ## No further information about a single row -/

/-- Under (M2), accident year `i` is independent of the other rows' observed
histories. -/
theorem indep_rowSigmaAll_otherObs (X : RandomTriangle Ω n) (hindep : RowsIndep X μ) (i : ℕ) :
    Indep (X.rowSigmaAll i) (X.otherObs i) μ :=
  indep_of_indep_of_le_right (indep_rowSigmaAll_otherRowsAll X hindep i)
    (X.otherObs_le_otherRowsAll i)

/-- **Conditioning on the whole triangle is conditioning on one row.** For a
variable carried by accident year `i`, the observed data adds nothing to that
year's own observed history:
`E[g | obsSigma] = E[g | rowSigma i (n-1-i)]`.

This is the content of Mack's phrase "because of the independence of the
accident years" in the proof of Theorem 3 (1993, p. 218). -/
theorem condExp_obsSigma_eq_rowSigma [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hindep : RowsIndep X μ) {i : ℕ} (hi : i < n) {g : Ω → ℝ}
    (hg : StronglyMeasurable[X.rowSigmaAll i] g) (hgint : Integrable g μ) :
    μ[g | X.obsSigma] =ᵐ[μ] μ[g | X.rowSigma i (n - 1 - i)] := by
  rw [X.obsSigma_eq_sup hi]
  exact condExp_sup_of_indep (X.rowSigma_le_rowSigmaAll i _) (X.rowSigmaAll_le i)
    (X.otherObs_le i) (indep_rowSigmaAll_otherObs X hindep i) hg hgint

/-- The same statement for the development-year filtration `D_k`: for a
variable carried by accident year `i`, conditioning on everything observed up
to development year `k` is conditioning on row `i`'s own history up to `k`. -/
theorem condExp_D_eq_rowSigma [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ) (i k : ℕ) {g : Ω → ℝ}
    (hg : StronglyMeasurable[X.rowSigmaAll i] g) (hgint : Integrable g μ) :
    μ[g | X.D k] =ᵐ[μ] μ[g | X.rowSigma i k] := by
  rw [X.D_eq_sup hgen i k]
  exact condExp_sup_of_indep (X.rowSigma_le_rowSigmaAll i k) (X.rowSigmaAll_le i)
    (X.otherRowsSigma_le i k) (indep_rowSigmaAll_otherRowsSigma X hindep i k) hg hgint

/-- **The hypothesis `hfut` of `condMsep_eq`, proved.** For a variable carried
by accident year `i`, the observed data and that year's development-year
filtration at its latest diagonal give the same conditional expectation. Both
reduce to the row's own observed history. -/
theorem condExp_obsSigma_eq_D [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ) {i : ℕ} (hi : i < n) {g : Ω → ℝ}
    (hg : StronglyMeasurable[X.rowSigmaAll i] g) (hgint : Integrable g μ) :
    μ[g | X.obsSigma] =ᵐ[μ] μ[g | X.D (n - 1 - i)] :=
  (condExp_obsSigma_eq_rowSigma X hindep hi hg hgint).trans
    (condExp_D_eq_rowSigma X hgen hindep i (n - 1 - i) hg hgint).symm

/-- `hfut1` of `condMsep_eq` for any entry of row `i`. -/
theorem condExp_C_obsSigma_eq_D [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ) {i : ℕ} (hi : i < n) (k : ℕ)
    (hC : Integrable (X.C i k) μ) :
    μ[X.C i k | X.obsSigma] =ᵐ[μ] μ[X.C i k | X.D (n - 1 - i)] :=
  condExp_obsSigma_eq_D X hgen hindep hi (X.stronglyMeasurable_rowSigmaAll i k) hC

/-- `hfut2` of `condMsep_eq` for any entry of row `i`. -/
theorem condExp_sq_C_obsSigma_eq_D [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ) {i : ℕ} (hi : i < n) (k : ℕ)
    (hCsq : Integrable (fun ω => (X.C i k ω) ^ 2) μ) :
    μ[fun ω => (X.C i k ω) ^ 2 | X.obsSigma]
      =ᵐ[μ] μ[fun ω => (X.C i k ω) ^ 2 | X.D (n - 1 - i)] :=
  condExp_obsSigma_eq_D X hgen hindep hi ((X.stronglyMeasurable_rowSigmaAll i k).pow 2) hCsq

/-! ## Mack's Theorem 3 from the row-conditioned assumptions -/

/-- **Mack's Theorem 3, exact form, from Mack's own assumptions.** Assume
(M1row) and (M3row) as Mack states them (conditioned on one accident year's own
history), independence across accident years (M2), that the development-year
filtration is generated by the rows' histories, and square integrability of the
claims and of the chain-ladder prediction. Then, conditionally on the observed
data,

`E[(Ĉ_{i,d+m} - C_{i,d+m})² | obsSigma] = procVar C_{i,d} f σ² d m + (Ĉ_{i,d+m} - M_m)²`

with `d = n-1-i` and `M_m = C_{i,d} ∏_{l<m} f_{d+l}`: process variance plus
squared estimation error, Mack (1993), Theorem 3 and its proof, pp. 217-219.
No hypothesis of `condMsep_eq` is left over: `hfut1` and `hfut2` come from
`condExp_obsSigma_eq_D`, the measurability of the predictor from
`stronglyMeasurable_obsSigma_ChatRv`, and (M1), (M3) in the `D_k` form from
`mack1_of_mack1Row` and `mack3_of_mack3Row`. -/
theorem condMsep_eq_of_rows [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f σ2 : ℕ → ℝ)
    (i m : ℕ) (hi : i < n)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ)
    (hrow1 : Mack1Row X μ f) (hrow3 : Mack3Row X μ f σ2)
    (hCmem : ∀ j k, MemLp (X.C j k) 2 μ)
    (hPmem : MemLp (X.ChatRv i m) 2 μ) :
    μ[fun ω => (X.ChatRv i m ω - X.C i (n - 1 - i + m) ω) ^ 2 | X.obsSigma]
      =ᵐ[μ] fun ω => procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) m
          + (X.ChatRv i m ω
              - X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1 - i + m), f l) ^ 2 := by
  have hC : ∀ j k, Integrable (X.C j k) μ := fun j k => (hCmem j k).integrable one_le_two
  have hCsq : ∀ j k, Integrable (fun ω => (X.C j k ω) ^ 2) μ :=
    fun j k => integrable_sq_of_memLp (hCmem j k)
  have hε2 : ∀ j k, Integrable (fun ω => (X.eps f j k ω) ^ 2) μ :=
    fun j k => integrable_sq_of_memLp (memLp_eps X f j k (hCmem j))
  have hM : Mack1 X μ f := mack1_of_mack1Row X f hgen hindep hrow1 hC
  have h3 : Mack3 X μ f σ2 := mack3_of_mack3Row X f σ2 hgen hindep hrow3 hε2
  exact condMsep_eq X f σ2 i m X.obsSigma_le (X.stronglyMeasurable_obsSigma_ChatRv hi m)
    (condExp_C_obsSigma_eq_D X hgen hindep hi _ (hC i _))
    (condExp_sq_C_obsSigma_eq_D X hgen hindep hi _ (hCsq i _))
    hi hM h3 (fun k => hC i k) (fun k => hCsq i k) (fun k => hε2 i k)
    (fun k => (hCmem i k).integrable_mul (memLp_eps X f i k (hCmem i)))
    (integrable_sq_of_memLp hPmem) (hPmem.integrable_mul (hCmem i _))

/-! ## The cross terms between accident years -/

/-- **The cross term of Mack's Corollary vanishes, one pair at a time.** For
`i ≠ j` with `i < n`, the centred true ultimates of the two accident years are
conditionally uncorrelated given the observed data.

The argument is the one used for (M2') in `mack2'_of_rows`. Condition on the
observed data together with the whole of accident year `j`: row `j`'s centred
ultimate is measurable there and comes out of the conditional expectation. What
is left is row `i`'s centred ultimate conditioned on a σ-algebra that adds
nothing about row `i` (`condExp_sup_of_indep`), and centring was by exactly
that conditional expectation, so it is zero. The tower property brings the
identity back to the observed data. -/
theorem condExp_cross_obsSigma_eq_zero [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hindep : RowsIndep X μ) (hCmem : ∀ j k, MemLp (X.C j k) 2 μ)
    {i j : ℕ} (hi : i < n) (hij : i ≠ j) :
    μ[fun ω => (X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
        * (X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω) | X.obsSigma] =ᵐ[μ] 0 := by
  have hC : ∀ j k, Integrable (X.C j k) μ := fun j k => (hCmem j k).integrable one_le_two
  have hm2le : X.otherObs i ⊔ X.rowSigmaAll j ≤ ‹MeasurableSpace Ω› :=
    sup_le (X.otherObs_le i) (X.rowSigmaAll_le j)
  have hbigle : X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)
      ≤ ‹MeasurableSpace Ω› := sup_le (X.rowSigma_le i _) hm2le
  have hobsle : X.obsSigma
      ≤ X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j) := by
    rw [X.obsSigma_eq_sup hi]
    exact sup_le_sup_left le_sup_left _
  have hindep' : Indep (X.rowSigmaAll i) (X.otherObs i ⊔ X.rowSigmaAll j) μ :=
    indep_of_indep_of_le_right (indep_rowSigmaAll_otherRowsAll X hindep i)
      (sup_le (X.otherObs_le_otherRowsAll i) (X.rowSigmaAll_le_otherRowsAll (Ne.symm hij)))
  -- the two centred ultimates
  have hWm : StronglyMeasurable[X.rowSigma i (n - 1 - i)]
      (μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]) := stronglyMeasurable_condExp
  have hWint : Integrable (μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]) μ := integrable_condExp
  have hZimem : MemLp (fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω) 2 μ :=
    (hCmem i (n - 1)).sub ((hCmem i (n - 1)).condExp one_le_two)
  have hZjmem : MemLp (fun ω => X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω) 2 μ :=
    (hCmem j (n - 1)).sub ((hCmem j (n - 1)).condExp one_le_two)
  have hZjm : StronglyMeasurable[X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)]
      (fun ω => X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω) := by
    refine StronglyMeasurable.sub ?_ ?_
    · exact (X.stronglyMeasurable_rowSigmaAll j (n - 1)).mono
        ((le_sup_right : X.rowSigmaAll j ≤ X.otherObs i ⊔ X.rowSigmaAll j).trans le_sup_right)
    · exact stronglyMeasurable_condExp.mono hobsle
  -- row `j`'s factor comes out of the enlarged conditional expectation
  have hstepA : μ[(fun ω => X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω)
        * (fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
        | X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)]
      =ᵐ[μ] (fun ω => X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω)
        * μ[(fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
            | X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)] :=
    condExp_mul_of_stronglyMeasurable_left hZjm (hZjmem.integrable_mul hZimem)
      (hZimem.integrable one_le_two)
  -- and what is left is row `i`'s centred ultimate, conditioned on nothing new
  have hMi : μ[X.C i (n - 1) | X.obsSigma]
      =ᵐ[μ] μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)] :=
    condExp_obsSigma_eq_rowSigma X hindep hi (X.stronglyMeasurable_rowSigmaAll i (n - 1))
      (hC i (n - 1))
  have hrow : μ[fun ω => X.C i (n - 1) ω
        - (μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]) ω | X.rowSigma i (n - 1 - i)]
      =ᵐ[μ] (0 : Ω → ℝ) := by
    have h1 := condExp_sub (hC i (n - 1)) hWint (X.rowSigma i (n - 1 - i))
    have h2 : μ[μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)] | X.rowSigma i (n - 1 - i)]
        = μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)] :=
      condExp_of_stronglyMeasurable (X.rowSigma_le i _) hWm hWint
    filter_upwards [h1] with ω hω
    have hval : (μ[X.C i (n - 1) - μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]
        | X.rowSigma i (n - 1 - i)]) ω = 0 := by
      rw [hω, Pi.sub_apply, h2, sub_self]
    exact hval
  have hstepB : μ[(fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
      | X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)] =ᵐ[μ] (0 : Ω → ℝ) := by
    have e1 : (fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
        =ᵐ[μ] fun ω => X.C i (n - 1) ω
          - (μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]) ω := by
      filter_upwards [hMi] with ω hω
      rw [hω]
    have e2 : μ[fun ω => X.C i (n - 1) ω
          - (μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]) ω
          | X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)]
        =ᵐ[μ] μ[fun ω => X.C i (n - 1) ω
          - (μ[X.C i (n - 1) | X.rowSigma i (n - 1 - i)]) ω | X.rowSigma i (n - 1 - i)] :=
      condExp_sup_of_indep (X.rowSigma_le_rowSigmaAll i _) (X.rowSigmaAll_le i) hm2le hindep'
        ((X.stronglyMeasurable_rowSigmaAll i (n - 1)).sub
          (hWm.mono (X.rowSigma_le_rowSigmaAll i _)))
        ((hC i (n - 1)).sub hWint)
    exact ((condExp_congr_ae e1).trans e2).trans hrow
  have hzero : μ[(fun ω => X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω)
      * (fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
      | X.rowSigma i (n - 1 - i) ⊔ (X.otherObs i ⊔ X.rowSigmaAll j)] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [hstepA, hstepB] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  -- tower back down to the observed data
  have hcomm : (fun ω => (X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω)
      * (X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω))
      = (fun ω => X.C j (n - 1) ω - (μ[X.C j (n - 1) | X.obsSigma]) ω)
        * (fun ω => X.C i (n - 1) ω - (μ[X.C i (n - 1) | X.obsSigma]) ω) := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  rw [hcomm]
  refine (condExp_condExp_of_le hobsle hbigle).symm.trans ?_
  refine (condExp_congr_ae hzero).trans ?_
  rw [condExp_zero]

/-- **`CondCrossFree` from independence across accident years.** The cross-term
condition that `TotalMsep.lean` takes as a hypothesis, and that Mack's Corollary
needs, is a consequence of (M2) together with square integrability of the
claims. -/
theorem condCrossFree_of_rows [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (hindep : RowsIndep X μ) (hCmem : ∀ j k, MemLp (X.C j k) 2 μ) :
    CondCrossFree μ X.obsSigma (range n) fun i => X.C i (n - 1) := by
  intro i hi j _ hij
  exact condExp_cross_obsSigma_eq_zero X hindep hCmem (Finset.mem_range.mp hi) hij

/-- **Mack's Corollary, exact form, from Mack's own assumptions.** Under
(M1row), (M3row), independence across accident years, the row-generated
filtration and square integrability, the conditional mean squared error of
prediction of the total of the chain-ladder ultimates splits, conditionally on
the observed data, into the sum of the single-year process variances and the
square of the summed estimation errors. Expanding that square is where the
cross terms of Mack (1993), Corollary to Theorem 3 (p. 220), come from. -/
theorem condMsepTotal_eq_of_rows [IsFiniteMeasure μ] (X : RandomTriangle Ω n) (f σ2 : ℕ → ℝ)
    (hgen : RowsGenerateD X) (hindep : RowsIndep X μ)
    (hrow1 : Mack1Row X μ f) (hrow3 : Mack3Row X μ f σ2)
    (hCmem : ∀ j k, MemLp (X.C j k) 2 μ)
    (hPmem : ∀ i, MemLp (X.ChatRv i i) 2 μ) :
    μ[fun ω => (∑ i ∈ range n, X.ChatRv i i ω - ∑ i ∈ range n, X.C i (n - 1) ω) ^ 2 | X.obsSigma]
      =ᵐ[μ] fun ω => (∑ i ∈ range n, procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) i)
        + (∑ i ∈ range n, (X.ChatRv i i ω
            - X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1), f l)) ^ 2 := by
  have hC : ∀ j k, Integrable (X.C j k) μ := fun j k => (hCmem j k).integrable one_le_two
  have hCsq : ∀ j k, Integrable (fun ω => (X.C j k ω) ^ 2) μ :=
    fun j k => integrable_sq_of_memLp (hCmem j k)
  have hε2 : ∀ j k, Integrable (fun ω => (X.eps f j k ω) ^ 2) μ :=
    fun j k => integrable_sq_of_memLp (memLp_eps X f j k (hCmem j))
  have hM : Mack1 X μ f := mack1_of_mack1Row X f hgen hindep hrow1 hC
  have h3 : Mack3 X μ f σ2 := mack3_of_mack3Row X f σ2 hgen hindep hrow3 hε2
  exact condMsepTotal_eq X f σ2 (range n) X.obsSigma_le (fun i hi => Finset.mem_range.mp hi)
    (fun i hi => X.stronglyMeasurable_obsSigma_ChatRv (Finset.mem_range.mp hi) i)
    (fun i _ => hPmem i) (fun i _ k => hCmem i k)
    (condCrossFree_of_rows X hindep hCmem)
    (fun i hi => condExp_C_obsSigma_eq_D X hgen hindep (Finset.mem_range.mp hi) _ (hC i _))
    (fun i hi => condExp_sq_C_obsSigma_eq_D X hgen hindep (Finset.mem_range.mp hi) _ (hCsq i _))
    hM h3

/-- **The exact total is at least the sum of the process variances**, from
Mack's own assumptions. -/
theorem sum_procVar_le_condMsepTotal_of_rows [IsFiniteMeasure μ] (X : RandomTriangle Ω n)
    (f σ2 : ℕ → ℝ) (hgen : RowsGenerateD X) (hindep : RowsIndep X μ)
    (hrow1 : Mack1Row X μ f) (hrow3 : Mack3Row X μ f σ2)
    (hCmem : ∀ j k, MemLp (X.C j k) 2 μ)
    (hPmem : ∀ i, MemLp (X.ChatRv i i) 2 μ) :
    (fun ω => ∑ i ∈ range n, procVar (X.C i (n - 1 - i) ω) f σ2 (n - 1 - i) i)
      ≤ᵐ[μ] μ[fun ω => (∑ i ∈ range n, X.ChatRv i i ω
          - ∑ i ∈ range n, X.C i (n - 1) ω) ^ 2 | X.obsSigma] := by
  filter_upwards [condMsepTotal_eq_of_rows X f σ2 hgen hindep hrow1 hrow3 hCmem hPmem] with ω hω
  rw [hω]
  nlinarith [sq_nonneg (∑ i ∈ range n, (X.ChatRv i i ω
    - X.C i (n - 1 - i) ω * ∏ l ∈ Ico (n - 1 - i) (n - 1), f l))]

end

end VerifiedReserving
