import VerifiedReserving.ChainLadder

/-!
# Chain ladder and the over-dispersed Poisson model

Renshaw and Verrall, *A stochastic model underlying the chain-ladder technique*,
British Actuarial Journal 4 (1998) 903-923, and Mack, *A simple parametric model
for rating automobile insurance or estimating IBNR claims reserves*, ASTIN
Bulletin 21 (1991) 93-109.

Write the triangle in incremental form, `X_{i,k} = C_{i,k} - C_{i,k-1}` with
`X_{i,0} = C_{i,0}`, and observe the cells with `i + k ≤ n-1`. The
over-dispersed Poisson (ODP) model of Renshaw and Verrall takes the incrementals
to be independent with mean `m_{i,k}` and variance `φ m_{i,k}`, and a log link
with a row effect and a column effect, so that the mean is multiplicative,
`m_{i,k} = a_i b_k`. Mack (1991) starts from the multiplicative mean directly.

Both papers estimate `a` and `b` from the *marginal-sum* (marginal-total)
equations: for every accident year `i` and every development year `k`,

  `∑_{k observed} m_{i,k} = ∑_{k observed} X_{i,k}` and
  `∑_{i observed} m_{i,k} = ∑_{i observed} X_{i,k}`.

These are the equations obtained by setting the derivatives of the quasi-Poisson
log-likelihood `∑ (X log m - m)/φ` in the row and column parameters to zero;
`deriv_rowQuasiLogLik_eq_zero_iff` and `deriv_colQuasiLogLik_eq_zero_iff` prove
that here, so the dispersion `φ` cancels and the name "score equations" is
earned rather than asserted. That cancellation is the reason chain ladder is
quoted as a generalized linear model: the fit does not depend on `φ`, only on
the mean structure, and the ODP fit is the Poisson fit.

What this file proves.

* `chainLadder_fitted_row_totals` and `chainLadder_fitted_column_totals`: the
  chain-ladder fitted incrementals satisfy the two marginal-sum equations, that
  is, chain ladder solves the ODP score equations. This is the content of
  Renshaw and Verrall (1998), Section 3, and of Mack (1991), Section 2.
* `multFit_eq_CLincr`: conversely, a multiplicative fit `a_i b_k` with positive
  parameters and `∑_{k<n} b_k = 1` that satisfies the marginal-sum equations
  *is* the chain-ladder fit, cell by cell. That is Mack's uniqueness result.

Source note. Neither paper was available in full text for this formalization.
What is formalized is the marginal-sum system as it is universally quoted (see
also England and Verrall, *Stochastic claims reserving in general insurance*,
British Actuarial Journal 8 (2002) 443-518, Section 2.3, and Wüthrich and Merz,
*Stochastic Claims Reserving Methods in Insurance* (2008), Section 2.3), stated
in the two papers' own terms. The displayed equations of the sources are
therefore named by section and by the display itself, not by number.

Everything here is deterministic: no probability space appears. The ODP
distributional assumption enters only through the shape of the score equations,
which are a system of algebraic identities in the fitted values.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-! ## The triangle in incremental form -/

/-- Incremental claims `X_{i,k} = C_{i,k} - C_{i,k-1}`, with `X_{i,0} = C_{i,0}`.
Renshaw and Verrall (1998) and Mack (1991) both model the incrementals; the
chain-ladder estimators of `ChainLadder.lean` are built from the cumulatives. -/
def incr (C : ℕ → ℕ → ℝ) (i k : ℕ) : ℝ :=
  if k = 0 then C i 0 else C i k - C i (k - 1)

/-- Development years observed for accident year `i`: those `k` with
`i + k ≤ n - 1`. -/
def obsRow (n i : ℕ) : Finset ℕ := range (n - i)

/-- Accident years observed at development year `k`: those `i` with
`i + k ≤ n - 1`. -/
def obsCol (n k : ℕ) : Finset ℕ := range (n - k)

theorem mem_obsRow {n i k : ℕ} (hi : i < n) : k ∈ obsRow n i ↔ i + k ≤ n - 1 := by
  simp only [obsRow, mem_range]
  omega

theorem mem_obsCol {n i k : ℕ} (hk : k < n) : i ∈ obsCol n k ↔ i + k ≤ n - 1 := by
  simp only [obsCol, mem_range]
  omega

/-- The accident years observed at development year `k+1` are exactly those
contributing to the development factor `k → k+1`. -/
theorem obsCol_succ (n k : ℕ) : obsCol n (k + 1) = contributors n k := by
  simp only [obsCol, contributors]
  congr 1

/-- Incrementals telescope: `∑_{k ≤ m} X_{i,k} = C_{i,m}`. -/
theorem sum_incr (C : ℕ → ℕ → ℝ) (i m : ℕ) :
    ∑ k ∈ range (m + 1), incr C i k = C i m := by
  induction m with
  | zero => simp [incr]
  | succ m ih =>
    have h : incr C i (m + 1) = C i (m + 1) - C i m := by simp [incr]
    rw [sum_range_succ, ih, h]
    ring

/-- The observed part of row `i` sums to the latest observed cumulative. -/
theorem sum_incr_obsRow (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    ∑ k ∈ obsRow n i, incr C i k = C i (n - 1 - i) := by
  have h : n - i = (n - 1 - i) + 1 := by omega
  rw [obsRow, h, sum_incr]

/-- The observed part of column `k+1` sums to `T_k - S_k`, the difference of the
two column sums of `ChainLadder.lean`. -/
theorem sum_incr_obsCol_succ (C : ℕ → ℕ → ℝ) (n k : ℕ) :
    ∑ i ∈ obsCol n (k + 1), incr C i (k + 1) = T C n k - S C n k := by
  rw [obsCol_succ]
  simp only [T, S, ← sum_sub_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  simp [incr]

/-! ## The chain-ladder fit on the observed triangle -/

/-- The chain-ladder fitted cumulative on an observed cell `(i,k)`, `k ≤ n-1-i`:
the latest observed entry of the row divided back by the development factors,
`C_{i,n-1-i} / ∏_{j=k}^{n-2-i} f̂_j`. Equivalently (`CLcum_eq_ultimate_div`) the
chain-ladder ultimate times the cumulative development pattern up to `k`, so
these are the `Chat` projections of `ChainLadder.lean` read backwards from the
latest diagonal. For `k ≥ n-1-i` the empty product makes this the latest
observed entry itself; only the observed range is used below. -/
def CLcum (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  C i (n - 1 - i) / ∏ j ∈ Ico k (n - 1 - i), fhat C n j

/-- The chain-ladder fitted incremental on an observed cell. -/
def CLincr (C : ℕ → ℕ → ℝ) (n i k : ℕ) : ℝ :=
  if k = 0 then CLcum C n i 0 else CLcum C n i k - CLcum C n i (k - 1)

/-- On the latest diagonal the fit reproduces the observation. -/
theorem CLcum_diag (C : ℕ → ℕ → ℝ) (n i : ℕ) :
    CLcum C n i (n - 1 - i) = C i (n - 1 - i) := by
  simp [CLcum]

/-- One step back along the row: `Ĉ_{i,k} = Ĉ_{i,k+1} / f̂_k`. -/
theorem CLcum_eq_div (C : ℕ → ℕ → ℝ) (n i k : ℕ) (hk : k < n - 1 - i) :
    CLcum C n i k = CLcum C n i (k + 1) / fhat C n k := by
  unfold CLcum
  rw [prod_eq_prod_Ico_succ_bot hk, div_div]
  ring_nf

/-- The fitted cumulatives are the `Chat` projections read backwards:
`Ĉ_{i,k} = Ĉ_{i,n-1} / ∏_{j=k}^{n-2} f̂_j`, the chain-ladder ultimate times the
cumulative development pattern up to development year `k`. -/
theorem CLcum_eq_ultimate_div (C : ℕ → ℕ → ℝ) (n i k : ℕ) (hk : k ≤ n - 1 - i)
    (hf : ∀ j, j < n - 1 → fhat C n j ≠ 0) :
    CLcum C n i k = ultimate C n i / ∏ j ∈ Ico k (n - 1), fhat C n j := by
  have hd : n - 1 - i ≤ n - 1 := by omega
  have hP : ∏ j ∈ Ico k (n - 1 - i), fhat C n j ≠ 0 := by
    refine prod_ne_zero_iff.mpr (fun j hj => hf j ?_)
    have hj' := (mem_Ico.mp hj).2
    omega
  have hQ : ∏ j ∈ Ico (n - 1 - i) (n - 1), fhat C n j ≠ 0 :=
    prod_ne_zero_iff.mpr (fun j hj => hf j (mem_Ico.mp hj).2)
  rw [CLcum, ultimate, Chat, ← prod_Ico_consecutive (fun j => fhat C n j) hk hd]
  field_simp

/-- Fitted incrementals telescope: `∑_{k ≤ m} X̂_{i,k} = Ĉ_{i,m}`. -/
theorem sum_CLincr (C : ℕ → ℕ → ℝ) (n i m : ℕ) :
    ∑ k ∈ range (m + 1), CLincr C n i k = CLcum C n i m := by
  induction m with
  | zero => simp [CLincr]
  | succ m ih =>
    have h : CLincr C n i (m + 1) = CLcum C n i (m + 1) - CLcum C n i m := by
      simp [CLincr]
    rw [sum_range_succ, ih, h]
    ring

/-! ## Chain ladder solves the marginal-sum equations -/

/-- **Row totals.** For every accident year `i`, the chain-ladder fitted
incrementals sum, over the observed development years, to the latest observed
cumulative `C_{i,n-1-i}`, which is also the observed row sum of incrementals.
This is the first family of marginal-sum equations of Mack (1991), Section 2,
and the row score equation of the ODP generalized linear model of Renshaw and
Verrall (1998), Section 3. It is an identity of the projection and needs no
hypothesis: the fitted values telescope back to the diagonal. -/
theorem chainLadder_fitted_row_totals (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    ∑ k ∈ obsRow n i, CLincr C n i k = C i (n - 1 - i) := by
  have h : n - i = (n - 1 - i) + 1 := by omega
  rw [obsRow, h, sum_CLincr, CLcum_diag]

/-- The row equation in marginal-sum form: the fitted row total equals the
observed row total. -/
theorem chainLadder_fitted_row_totals_eq (C : ℕ → ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    ∑ k ∈ obsRow n i, CLincr C n i k = ∑ k ∈ obsRow n i, incr C i k := by
  rw [chainLadder_fitted_row_totals C n i hi, sum_incr_obsRow C n i hi]

/-- The fitted cumulatives of a whole observed column sum to the observed column
sum of cumulatives. This is the step behind the column marginal-sum equations;
it is proved by downward induction on `k`, the induction step being exactly the
definition of `f̂_k` as the ratio of the two column sums. -/
theorem sum_CLcum_obsCol_aux (C : ℕ → ℕ → ℝ) (n : ℕ)
    (hf : ∀ j, j < n - 1 → fhat C n j ≠ 0) :
    ∀ d k : ℕ, k + d = n - 1 →
      ∑ i ∈ obsCol n k, CLcum C n i k = ∑ i ∈ obsCol n k, C i k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [obsCol]
    · have hk' : k = n - 1 := by omega
      subst hk'
      have h1 : n - (n - 1) = 1 := by omega
      simp only [obsCol, h1, sum_range_one]
      have h2 : n - 1 - 0 = n - 1 := by omega
      rw [CLcum, h2]
      simp
  | succ d ih =>
    intro k hk
    have hkn : k < n - 1 := by omega
    have hk1 : k + 1 + d = n - 1 := by omega
    have hcon : contributors n k = range (n - k - 1) := rfl
    have hstep : ∑ i ∈ range (n - k - 1), CLcum C n i k = S C n k := by
      have hcong : ∀ i ∈ range (n - k - 1),
          CLcum C n i k = CLcum C n i (k + 1) / fhat C n k := by
        intro i hi
        have hi' := mem_range.mp hi
        exact CLcum_eq_div C n i k (by omega)
      rw [sum_congr rfl hcong, ← sum_div]
      have hIH : ∑ i ∈ range (n - k - 1), CLcum C n i (k + 1) = T C n k := by
        have h := ih (k + 1) hk1
        rw [obsCol_succ, hcon] at h
        rw [h]
        rfl
      rw [hIH]
      have hfk := hf k hkn
      have hTne : T C n k ≠ 0 := (div_ne_zero_iff.mp hfk).1
      rw [fhat, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hTne, mul_one]
    have hdiag : CLcum C n (n - k - 1) k = C (n - k - 1) k := by
      have h1 : n - 1 - (n - k - 1) = k := by omega
      rw [CLcum, h1]
      simp
    have hsplit : ∀ f : ℕ → ℝ,
        ∑ i ∈ obsCol n k, f i = (∑ i ∈ range (n - k - 1), f i) + f (n - k - 1) := by
      intro f
      have hset : obsCol n k = range ((n - k - 1) + 1) := by
        simp only [obsCol]
        congr 1
        omega
      rw [hset, sum_range_succ]
    rw [hsplit, hsplit, hstep, hdiag]
    simp only [S, contributors]

/-- The column identity of `sum_CLcum_obsCol_aux`, stated for a development year
directly. -/
theorem sum_CLcum_obsCol (C : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k ≤ n - 1)
    (hf : ∀ j, j < n - 1 → fhat C n j ≠ 0) :
    ∑ i ∈ obsCol n k, CLcum C n i k = ∑ i ∈ obsCol n k, C i k :=
  sum_CLcum_obsCol_aux C n hf (n - 1 - k) k (by omega)

/-- One development year earlier, over the same accident years: the fitted
cumulatives at `k` sum, over the accident years contributing to `f̂_k`, to the
column sum `S_k`. -/
theorem sum_CLcum_contributors (C : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k < n - 1)
    (hf : ∀ j, j < n - 1 → fhat C n j ≠ 0) :
    ∑ i ∈ contributors n k, CLcum C n i k = S C n k := by
  have hcon : contributors n k = range (n - k - 1) := rfl
  have hcong : ∀ i ∈ range (n - k - 1),
      CLcum C n i k = CLcum C n i (k + 1) / fhat C n k := by
    intro i hi
    have hi' := mem_range.mp hi
    exact CLcum_eq_div C n i k (by omega)
  rw [hcon, sum_congr rfl hcong, ← sum_div]
  have hIH : ∑ i ∈ range (n - k - 1), CLcum C n i (k + 1) = T C n k := by
    have h := sum_CLcum_obsCol C n (k + 1) (by omega) hf
    rw [obsCol_succ, hcon] at h
    rw [h]
    rfl
  rw [hIH]
  have hfk := hf k hk
  have hTne : T C n k ≠ 0 := (div_ne_zero_iff.mp hfk).1
  rw [fhat, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hTne, mul_one]

/-- **Column totals.** For every development year `k`, the chain-ladder fitted
incrementals sum, over the observed accident years, to the observed column sum
of incrementals. This is the second family of marginal-sum equations of Mack
(1991), Section 2, and the column score equation of the ODP generalized linear
model of Renshaw and Verrall (1998), Section 3. The hypothesis is the one that
makes the chain-ladder factors defined and invertible: every development factor
used is nonzero, which by `div_ne_zero_iff` also gives the nonvanishing column
sums `S_j` of `ChainLadder.lean`. -/
theorem chainLadder_fitted_column_totals (C : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k < n)
    (hf : ∀ j, j < n - 1 → fhat C n j ≠ 0) :
    ∑ i ∈ obsCol n k, CLincr C n i k = ∑ i ∈ obsCol n k, incr C i k := by
  cases k with
  | zero =>
    have h := sum_CLcum_obsCol C n 0 (by omega) hf
    simpa [CLincr, incr] using h
  | succ m =>
    have h1 := sum_CLcum_obsCol C n (m + 1) (by omega) hf
    have h2 := sum_CLcum_contributors C n m (by omega) hf
    have hCL : ∀ i ∈ obsCol n (m + 1),
        CLincr C n i (m + 1) = CLcum C n i (m + 1) - CLcum C n i m := by
      intro i _
      simp [CLincr]
    have hX : ∀ i ∈ obsCol n (m + 1), incr C i (m + 1) = C i (m + 1) - C i m := by
      intro i _
      simp [incr]
    rw [sum_congr rfl hCL, sum_congr rfl hX, sum_sub_distrib, sum_sub_distrib, h1,
      obsCol_succ, h2]
    simp only [S, contributors]

/-! ## The multiplicative model and the score equations -/

/-- The multiplicative mean of Renshaw and Verrall (1998) and Mack (1991):
`m_{i,k} = a_i b_k`, the exponential of a row effect plus a column effect. -/
def multFit (a b : ℕ → ℝ) (i k : ℕ) : ℝ := a i * b k

/-- The identifiability constraint `∑_{k<n} b_k = 1`: the column effects are a
development pattern, and the row effect `a_i` is then the fitted ultimate of
accident year `i`. -/
def PatternNormalized (b : ℕ → ℝ) (n : ℕ) : Prop := ∑ k ∈ range n, b k = 1

/-- The cumulative development pattern `B_k = ∑_{j ≤ k} b_j`. -/
def patternCum (b : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), b j

/-- Row marginal sums: for every accident year, the fitted values sum over the
observed development years to the observed incrementals. -/
def RowTotals (m C : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i, i < n → ∑ k ∈ obsRow n i, m i k = ∑ k ∈ obsRow n i, incr C i k

/-- Column marginal sums: for every development year, the fitted values sum over
the observed accident years to the observed incrementals. -/
def ColumnTotals (m C : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ k, k < n → ∑ i ∈ obsCol n k, m i k = ∑ i ∈ obsCol n k, incr C i k

/-- The ODP score equations, that is Mack's marginal-sum system: the row and
column marginal totals of the fitted values equal those of the observations. -/
def ScoreEquations (m C : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  RowTotals m C n ∧ ColumnTotals m C n

/-- **Chain ladder solves the ODP score equations.** Both marginal-sum families
of Mack (1991), Section 2, and Renshaw and Verrall (1998), Section 3, hold for
the chain-ladder fitted incrementals. -/
theorem chainLadder_scoreEquations (C : ℕ → ℕ → ℝ) (n : ℕ)
    (hf : ∀ j, j < n - 1 → fhat C n j ≠ 0) :
    ScoreEquations (CLincr C n) C n :=
  ⟨fun i hi => chainLadder_fitted_row_totals_eq C n i hi,
   fun k hk => chainLadder_fitted_column_totals C n k hk hf⟩

/-! ## The score equations are the score equations

The quasi-Poisson log-likelihood of the observed triangle is
`∑_{(i,k) observed} (X_{i,k} log m_{i,k} - m_{i,k}) / φ`. Its derivative in a
single row parameter, the other parameters held fixed, is the row marginal
residual divided by that parameter; likewise for a column parameter. The
dispersion `φ` is a positive constant and cancels, which is why the
over-dispersed Poisson fit and the Poisson fit coincide; it is set to `1`
below. -/

/-- The quasi-Poisson log-likelihood of the observed part of accident year `i`
as a function of the row parameter. -/
def rowQuasiLogLik (C : ℕ → ℕ → ℝ) (n i : ℕ) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ obsRow n i, (incr C i k * Real.log (t * b k) - t * b k)

/-- The quasi-Poisson log-likelihood of the observed part of development year
`k` as a function of the column parameter. -/
def colQuasiLogLik (C : ℕ → ℕ → ℝ) (n k : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ obsCol n k, (incr C i k * Real.log (a i * t) - a i * t)

/-- The row score: the derivative of the quasi-Poisson log-likelihood in the row
parameter is the row marginal residual divided by that parameter. -/
theorem hasDerivAt_rowQuasiLogLik (C : ℕ → ℕ → ℝ) (n i : ℕ) (b : ℕ → ℝ) (t : ℝ)
    (ht : t ≠ 0) (hb : ∀ k ∈ obsRow n i, b k ≠ 0) :
    HasDerivAt (rowQuasiLogLik C n i b)
      ((∑ k ∈ obsRow n i, incr C i k - ∑ k ∈ obsRow n i, t * b k) / t) t := by
  have h : ∀ k ∈ obsRow n i,
      HasDerivAt (fun s : ℝ => incr C i k * Real.log (s * b k) - s * b k)
        (incr C i k / t - b k) t := by
    intro k hk
    have hbk := hb k hk
    have h1 : HasDerivAt (fun s : ℝ => s * b k) (1 * b k) t :=
      (hasDerivAt_id t).mul_const (b k)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (s * b k)) (1 * b k / (t * b k)) t :=
      h1.log (mul_ne_zero ht hbk)
    have h3 := (h2.const_mul (incr C i k)).sub h1
    have h4 : incr C i k * (1 * b k / (t * b k)) - 1 * b k = incr C i k / t - b k := by
      field_simp
    rwa [h4] at h3
  have key : ∑ k ∈ obsRow n i, (incr C i k / t - b k)
      = (∑ k ∈ obsRow n i, incr C i k - ∑ k ∈ obsRow n i, t * b k) / t := by
    rw [sum_sub_distrib, ← sum_div, sub_div, ← mul_sum, mul_div_cancel_left₀ _ ht]
  rw [← key]
  exact HasDerivAt.fun_sum h

/-- The column score: the derivative of the quasi-Poisson log-likelihood in the
column parameter is the column marginal residual divided by that parameter. -/
theorem hasDerivAt_colQuasiLogLik (C : ℕ → ℕ → ℝ) (n k : ℕ) (a : ℕ → ℝ) (t : ℝ)
    (ht : t ≠ 0) (ha : ∀ i ∈ obsCol n k, a i ≠ 0) :
    HasDerivAt (colQuasiLogLik C n k a)
      ((∑ i ∈ obsCol n k, incr C i k - ∑ i ∈ obsCol n k, a i * t) / t) t := by
  have h : ∀ i ∈ obsCol n k,
      HasDerivAt (fun s : ℝ => incr C i k * Real.log (a i * s) - a i * s)
        (incr C i k / t - a i) t := by
    intro i hi
    have hai := ha i hi
    have h1 : HasDerivAt (fun s : ℝ => a i * s) (a i * 1) t :=
      (hasDerivAt_id t).const_mul (a i)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (a i * s)) (a i * 1 / (a i * t)) t :=
      h1.log (mul_ne_zero hai ht)
    have h3 := (h2.const_mul (incr C i k)).sub h1
    have h4 : incr C i k * (a i * 1 / (a i * t)) - a i * 1 = incr C i k / t - a i := by
      field_simp
    rwa [h4] at h3
  have key : ∑ i ∈ obsCol n k, (incr C i k / t - a i)
      = (∑ i ∈ obsCol n k, incr C i k - ∑ i ∈ obsCol n k, a i * t) / t := by
    rw [sum_sub_distrib, ← sum_div, sub_div, ← sum_mul, mul_comm,
      mul_div_cancel_left₀ _ ht]
  rw [← key]
  exact HasDerivAt.fun_sum h

/-- The row score vanishes exactly at the row marginal-sum equation: the row
equations of `RowTotals` are the stationarity conditions of the quasi-Poisson
log-likelihood in the row parameters. -/
theorem deriv_rowQuasiLogLik_eq_zero_iff (C : ℕ → ℕ → ℝ) (n i : ℕ) (a b : ℕ → ℝ)
    (ha : a i ≠ 0) (hb : ∀ k ∈ obsRow n i, b k ≠ 0) :
    deriv (rowQuasiLogLik C n i b) (a i) = 0 ↔
      ∑ k ∈ obsRow n i, multFit a b i k = ∑ k ∈ obsRow n i, incr C i k := by
  rw [(hasDerivAt_rowQuasiLogLik C n i b (a i) ha hb).deriv, div_eq_zero_iff,
    sub_eq_zero, or_iff_left ha]
  simp only [multFit]
  exact eq_comm

/-- The column score vanishes exactly at the column marginal-sum equation. -/
theorem deriv_colQuasiLogLik_eq_zero_iff (C : ℕ → ℕ → ℝ) (n k : ℕ) (a b : ℕ → ℝ)
    (hb : b k ≠ 0) (ha : ∀ i ∈ obsCol n k, a i ≠ 0) :
    deriv (colQuasiLogLik C n k a) (b k) = 0 ↔
      ∑ i ∈ obsCol n k, multFit a b i k = ∑ i ∈ obsCol n k, incr C i k := by
  rw [(hasDerivAt_colQuasiLogLik C n k a (b k) hb ha).deriv, div_eq_zero_iff,
    sub_eq_zero, or_iff_left hb]
  simp only [multFit]
  exact eq_comm

/-! ## Uniqueness: a multiplicative marginal-sum fit is the chain-ladder fit -/

/-- The fitted row total of a multiplicative model is `a_i B_{n-1-i}`. -/
theorem sum_multFit_obsRow (n i : ℕ) (a b : ℕ → ℝ) (hi : i < n) :
    ∑ k ∈ obsRow n i, multFit a b i k = a i * patternCum b (n - 1 - i) := by
  have h : n - i = (n - 1 - i) + 1 := by omega
  simp only [obsRow, multFit, patternCum, h, ← mul_sum]

/-- The fitted column total of a multiplicative model is `(∑ a_i) b_k`. -/
theorem sum_multFit_obsCol (n k : ℕ) (a b : ℕ → ℝ) :
    ∑ i ∈ obsCol n k, multFit a b i k = (∑ i ∈ obsCol n k, a i) * b k := by
  simp only [multFit, sum_mul]

/-- The row marginal-sum equation in closed form, `a_i B_{n-1-i} = C_{i,n-1-i}`.
With `∑_{k<n} b_k = 1` this says that `a_i` is the fitted ultimate of accident
year `i`. -/
theorem mult_row_eq (C : ℕ → ℕ → ℝ) (n : ℕ) (a b : ℕ → ℝ)
    (hsc : ScoreEquations (multFit a b) C n) (i : ℕ) (hi : i < n) :
    a i * patternCum b (n - 1 - i) = C i (n - 1 - i) := by
  have h := hsc.1 i hi
  rwa [sum_multFit_obsRow n i a b hi, sum_incr_obsRow C n i hi] at h

/-- The column identity for a multiplicative marginal-sum fit, the analogue of
`sum_CLcum_obsCol_aux`: the fitted cumulatives `a_i B_k` reproduce the observed
column sums of cumulatives. Downward induction on `k`. -/
theorem sum_mult_patternCum_aux (C : ℕ → ℕ → ℝ) (n : ℕ) (a b : ℕ → ℝ)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n) :
    ∀ d k : ℕ, k + d = n - 1 →
      ∑ i ∈ obsCol n k, a i * patternCum b k = ∑ i ∈ obsCol n k, C i k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [obsCol]
    · have hk' : k = n - 1 := by omega
      subst hk'
      have h1 : n - (n - 1) = 1 := by omega
      have hB : patternCum b (n - 1) = 1 := by
        have h2 : n - 1 + 1 = n := by omega
        rw [patternCum, h2]
        exact hnorm
      have hrow := mult_row_eq C n a b hsc 0 (by omega)
      have h3 : n - 1 - 0 = n - 1 := by omega
      rw [h3] at hrow
      simp only [obsCol, h1, sum_range_one]
      exact hrow
  | succ d ih =>
    intro k hk
    have hkn : k < n - 1 := by omega
    have hk1 : k + 1 + d = n - 1 := by omega
    have hkn1 : k + 1 < n := by omega
    have hcon : contributors n k = range (n - k - 1) := rfl
    have hIH : (∑ i ∈ range (n - k - 1), a i) * patternCum b (k + 1) = T C n k := by
      have h := ih (k + 1) hk1
      rw [obsCol_succ, hcon] at h
      rw [sum_mul, h]
      rfl
    have hcol : (∑ i ∈ range (n - k - 1), a i) * b (k + 1) = T C n k - S C n k := by
      have h := hsc.2 (k + 1) hkn1
      rw [sum_multFit_obsCol, sum_incr_obsCol_succ, obsCol_succ, hcon] at h
      exact h
    have hsplitB : patternCum b (k + 1) = patternCum b k + b (k + 1) := by
      simp [patternCum, sum_range_succ]
    have hAB : ∑ i ∈ range (n - k - 1), a i * patternCum b k = S C n k := by
      rw [hsplitB, mul_add] at hIH
      rw [← sum_mul]
      linarith
    have hdiag : a (n - k - 1) * patternCum b k = C (n - k - 1) k := by
      have hrow := mult_row_eq C n a b hsc (n - k - 1) (by omega)
      have h1 : n - 1 - (n - k - 1) = k := by omega
      rwa [h1] at hrow
    have hsplit : ∀ f : ℕ → ℝ,
        ∑ i ∈ obsCol n k, f i = (∑ i ∈ range (n - k - 1), f i) + f (n - k - 1) := by
      intro f
      have hset : obsCol n k = range ((n - k - 1) + 1) := by
        simp only [obsCol]
        congr 1
        omega
      rw [hset, sum_range_succ]
    rw [hsplit, hsplit, hAB, hdiag]
    simp only [S, contributors]

/-- The column identity of `sum_mult_patternCum_aux`, stated for a development
year directly. -/
theorem sum_mult_patternCum (C : ℕ → ℕ → ℝ) (n k : ℕ) (a b : ℕ → ℝ)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n)
    (hk : k ≤ n - 1) :
    ∑ i ∈ obsCol n k, a i * patternCum b k = ∑ i ∈ obsCol n k, C i k :=
  sum_mult_patternCum_aux C n a b hnorm hsc (n - 1 - k) k (by omega)

/-- The cumulative pattern is positive on the observed range. -/
theorem patternCum_pos (b : ℕ → ℝ) (n k : ℕ) (hk : k < n)
    (hb : ∀ j, j < n → 0 < b j) : 0 < patternCum b k := by
  refine sum_pos (fun j hj => hb j ?_) ⟨0, mem_range.mpr (Nat.succ_pos k)⟩
  have hj' := mem_range.mp hj
  omega

/-- **The development factors of a multiplicative marginal-sum fit are the
chain-ladder factors:** `B_{k+1} / B_k = f̂_k`, in the form
`B_k f̂_k = B_{k+1}`. This is the step of Mack (1991), Section 2, that
identifies the marginal-sum solution with chain ladder. -/
theorem patternCum_mul_fhat (C : ℕ → ℕ → ℝ) (n k : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i, i < n → 0 < a i) (hb : ∀ j, j < n → 0 < b j)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n)
    (hk : k < n - 1) :
    patternCum b k * fhat C n k = patternCum b (k + 1) := by
  have hcon : contributors n k = range (n - k - 1) := rfl
  have hkn1 : k + 1 < n := by omega
  have hA : 0 < ∑ i ∈ range (n - k - 1), a i := by
    refine sum_pos (fun i hi => ha i ?_) ⟨0, mem_range.mpr (by omega)⟩
    have hi' := mem_range.mp hi
    omega
  have hBk : 0 < patternCum b k := patternCum_pos b n k (by omega) hb
  have hAne : (∑ i ∈ range (n - k - 1), a i) ≠ 0 := ne_of_gt hA
  have hBkne : patternCum b k ≠ 0 := ne_of_gt hBk
  have hIH : (∑ i ∈ range (n - k - 1), a i) * patternCum b (k + 1) = T C n k := by
    have h := sum_mult_patternCum C n (k + 1) a b hnorm hsc (by omega)
    rw [obsCol_succ, hcon] at h
    rw [sum_mul, h]
    rfl
  have hcol : (∑ i ∈ range (n - k - 1), a i) * b (k + 1) = T C n k - S C n k := by
    have h := hsc.2 (k + 1) hkn1
    rw [sum_multFit_obsCol, sum_incr_obsCol_succ, obsCol_succ, hcon] at h
    exact h
  have hsplitB : patternCum b (k + 1) = patternCum b k + b (k + 1) := by
    simp [patternCum, sum_range_succ]
  have hAB : (∑ i ∈ range (n - k - 1), a i) * patternCum b k = S C n k := by
    rw [hsplitB, mul_add] at hIH
    linarith
  rw [fhat, ← hIH, ← hAB]
  field_simp

/-- Telescoping the pattern ratios: `B_k ∏_{j=k}^{k+d-1} f̂_j = B_{k+d}`. -/
theorem patternCum_mul_prod (C : ℕ → ℕ → ℝ) (n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i, i < n → 0 < a i) (hb : ∀ j, j < n → 0 < b j)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n) :
    ∀ d k : ℕ, k + d ≤ n - 1 →
      patternCum b k * ∏ j ∈ Ico k (k + d), fhat C n j = patternCum b (k + d) := by
  intro d
  induction d with
  | zero => intro k _; simp
  | succ d ih =>
    intro k hk
    have h1 : k ≤ k + d := Nat.le_add_right k d
    have h2 : k + (d + 1) = k + d + 1 := by omega
    rw [h2, prod_Ico_succ_top h1, ← mul_assoc, ih k (by omega)]
    exact patternCum_mul_fhat C n (k + d) a b ha hb hnorm hsc (by omega)

/-- Every development factor of a positive multiplicative marginal-sum fit is
positive. -/
theorem fhat_pos_of_mult (C : ℕ → ℕ → ℝ) (n k : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i, i < n → 0 < a i) (hb : ∀ j, j < n → 0 < b j)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n)
    (hk : k < n - 1) : 0 < fhat C n k := by
  have h := patternCum_mul_fhat C n k a b ha hb hnorm hsc hk
  have hBk : 0 < patternCum b k := patternCum_pos b n k (by omega) hb
  have hBk1 : 0 < patternCum b (k + 1) := patternCum_pos b n (k + 1) (by omega) hb
  nlinarith

/-- **Mack's uniqueness result, cumulative form.** A positive multiplicative
model with `∑_{k<n} b_k = 1` satisfying the marginal-sum equations has fitted
cumulatives `a_i B_k` equal to the chain-ladder fitted cumulatives on every
observed cell. -/
theorem mult_cum_eq_CLcum (C : ℕ → ℕ → ℝ) (n i k : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ j, j < n → 0 < a j) (hb : ∀ j, j < n → 0 < b j)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n)
    (hi : i < n) (hik : i + k ≤ n - 1) :
    a i * patternCum b k = CLcum C n i k := by
  have hd : k + (n - 1 - i - k) = n - 1 - i := by omega
  have hprod := patternCum_mul_prod C n a b ha hb hnorm hsc (n - 1 - i - k) k (by omega)
  rw [hd] at hprod
  have hne : ∏ j ∈ Ico k (n - 1 - i), fhat C n j ≠ 0 := by
    refine prod_ne_zero_iff.mpr (fun j hj => ne_of_gt ?_)
    have hj' := mem_Ico.mp hj
    exact fhat_pos_of_mult C n j a b ha hb hnorm hsc (by omega)
  have hrow := mult_row_eq C n a b hsc i hi
  rw [CLcum, eq_div_iff hne, mul_assoc, hprod, hrow]

/-- **Mack's uniqueness result (Mack 1991, Section 2).** A positive
multiplicative model `m_{i,k} = a_i b_k` with `∑_{k<n} b_k = 1` that satisfies
the marginal-sum (ODP score) equations coincides, cell by cell on the observed
triangle, with the chain-ladder fit. Together with `chainLadder_scoreEquations`
this is the classical statement that the over-dispersed Poisson generalized
linear model and the chain-ladder method give the same fitted values, hence the
same reserves. -/
theorem multFit_eq_CLincr (C : ℕ → ℕ → ℝ) (n i k : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ j, j < n → 0 < a j) (hb : ∀ j, j < n → 0 < b j)
    (hnorm : PatternNormalized b n) (hsc : ScoreEquations (multFit a b) C n)
    (hi : i < n) (hik : i + k ≤ n - 1) :
    multFit a b i k = CLincr C n i k := by
  cases k with
  | zero =>
    have h := mult_cum_eq_CLcum C n i 0 a b ha hb hnorm hsc hi hik
    have hp : patternCum b 0 = b 0 := by simp [patternCum]
    rw [hp] at h
    simpa [multFit, CLincr] using h
  | succ m =>
    have h1 := mult_cum_eq_CLcum C n i (m + 1) a b ha hb hnorm hsc hi hik
    have h2 := mult_cum_eq_CLcum C n i m a b ha hb hnorm hsc hi (by omega)
    have hsplitB : patternCum b (m + 1) = patternCum b m + b (m + 1) := by
      simp [patternCum, sum_range_succ]
    rw [hsplitB, mul_add] at h1
    have hCL : CLincr C n i (m + 1) = CLcum C n i (m + 1) - CLcum C n i m := by
      simp [CLincr]
    rw [hCL, multFit]
    linarith

end

end VerifiedReserving
