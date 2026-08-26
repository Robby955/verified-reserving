import VerifiedReserving.BFPriorUncertainty
import VerifiedReserving.ODP

/-!
# The stochastic Bornhuetter-Ferguson model and prediction error

Mack (2008), "The Prediction Error of Bornhuetter/Ferguson," pp. 91 and
95-99, models the incremental claims `S i k` by three assumptions:

* (BF1) all increments are independent;
* (BF2) `E[S i k] = x i * y k`, with the development proportions summing to one;
* (BF3) `Var(S i k) = x i * sigma2 k`.

The exact results below give the mean and variance of a future row sum, the
variance of a BF estimate with independent random prior and development
pattern, and the single-row MSEP split into estimation and process variance.

The raw pattern and dispersion estimators from Section 4 are proved unbiased;
the raw pattern estimator is also proved best among linear unbiased estimators.
The plug-in assessment formulas remain definitions. In particular, smoothing
and tail selection, the minimum used for the pattern standard error, and the
omitted middle covariance term are not promoted to probability theorems.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace VerifiedReserving

noncomputable section

variable {Omega : Type*} {G : MeasurableSpace Omega} [mOmega : MeasurableSpace Omega]
  {mu : Measure Omega} {n : Nat}

/-! ## Mack's BF1-BF3 increment model -/

/-- The random incremental claim in cell `(i,k)`, with development years
numbered from zero. -/
def RandomTriangle.bfIncrementRv (X : RandomTriangle Omega n) (i k : Nat) : Omega -> Real :=
  fun omega => incr (X.at omega) i k

/-- Mack (2008), BF1: all accident-year/development-year increments are
independent. The source imposes this on the finite modeled rectangle; using the
full family makes every finite restriction available directly. -/
def BFFullIncrementIndependence
    (X : RandomTriangle Omega n) (mu : Measure Omega) : Prop :=
  iIndepFun (fun p : Nat × Nat => X.bfIncrementRv p.1 p.2) mu

/-- Mack (2008), BF2 on a finite horizon: `E[S i k] = x i * y k`. -/
def BFIncrementMean (X : RandomTriangle Omega n) (mu : Measure Omega)
    (x y : Nat -> Real) (m : Nat) : Prop :=
  forall i, i < n -> forall k, k < m ->
    integral mu (X.bfIncrementRv i k) = x i * y k

/-- Mack (2008), BF3 on a finite horizon: `Var(S i k) = x i * sigma2 k`. -/
def BFIncrementVariance (X : RandomTriangle Omega n) (mu : Measure Omega)
    (x sigma2 : Nat -> Real) (m : Nat) : Prop :=
  forall i, i < n -> forall k, k < m ->
    variance (X.bfIncrementRv i k) mu = x i * sigma2 k

/-- BF2's normalization of the development proportions on the modeled
horizon. -/
def BFPatternNormalized (y : Nat -> Real) (m : Nat) : Prop :=
  Finset.sum (range m) y = 1

/-- Cumulative expected-reported proportion through the first `d`
zero-based development periods. -/
def bfCumulativePattern (y : Nat -> Real) (d : Nat) : Real :=
  Finset.sum (range d) y

/-- The true future reserve from development period `d` through `m-1`. -/
def RandomTriangle.bfFutureReserveRv
    (X : RandomTriangle Omega n) (i d m : Nat) : Omega -> Real :=
  Finset.sum (Ico d m) fun k => X.bfIncrementRv i k

/-- Under BF2, the expected future reserve is the volume times the sum of the
remaining development proportions. -/
theorem integral_bfFutureReserveRv_eq_tail
    (X : RandomTriangle Omega n) (x y : Nat -> Real) (i d m : Nat)
    (hi : i < n) (hmean : BFIncrementMean X mu x y m)
    (hint : forall k, k ∈ Ico d m -> Integrable (X.bfIncrementRv i k) mu) :
    integral mu (X.bfFutureReserveRv i d m) = x i * Finset.sum (Ico d m) y := by
  rw [RandomTriangle.bfFutureReserveRv]
  rw [show Finset.sum (Ico d m) (fun k => X.bfIncrementRv i k) =
      fun omega => Finset.sum (Ico d m) fun k => X.bfIncrementRv i k omega by
    funext omega
    exact Finset.sum_apply omega (Ico d m) fun k => X.bfIncrementRv i k]
  rw [integral_finsetSum _ hint]
  rw [Finset.sum_congr rfl fun k hk => hmean i hi k (mem_Ico.mp hk).2]
  rw [mul_sum]

/-- Mack (2008), p. 91: after normalizing the development proportions, the
expected future reserve has the BF form `x i * (1 - z d)`. -/
theorem integral_bfFutureReserveRv
    (X : RandomTriangle Omega n) (x y : Nat -> Real) (i d m : Nat)
    (hi : i < n) (hdm : d <= m) (hnorm : BFPatternNormalized y m)
    (hmean : BFIncrementMean X mu x y m)
    (hint : forall k, k ∈ Ico d m -> Integrable (X.bfIncrementRv i k) mu) :
    integral mu (X.bfFutureReserveRv i d m) =
      x i * (1 - bfCumulativePattern y d) := by
  rw [integral_bfFutureReserveRv_eq_tail X x y i d m hi hmean hint]
  unfold BFPatternNormalized at hnorm
  unfold bfCumulativePattern
  rw [Finset.sum_Ico_eq_sub _ hdm, hnorm]

/-- Under BF1 and BF3, variances of the independent future increments add. -/
theorem variance_bfFutureReserveRv
    (X : RandomTriangle Omega n) (x sigma2 : Nat -> Real) (i d m : Nat)
    (hi : i < n) (hindep : BFFullIncrementIndependence X mu)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hmem : forall k, k ∈ Ico d m -> MemLp (X.bfIncrementRv i k) 2 mu) :
    variance (X.bfFutureReserveRv i d m) mu =
      x i * Finset.sum (Ico d m) sigma2 := by
  rw [RandomTriangle.bfFutureReserveRv]
  rw [IndepFun.variance_sum hmem]
  · rw [Finset.sum_congr rfl fun k hk => hvar i hi k (mem_Ico.mp hk).2]
    rw [mul_sum]
  · intro k hk l hl hkl
    have hp : (i, k) ≠ (i, l) := by
      intro hpairs
      exact hkl (Prod.mk.inj hpairs).2
    unfold BFFullIncrementIndependence at hindep
    exact hindep.indepFun hp

/-! ## Exact product variance and the single-row MSEP -/

/-- A stochastic BF estimate `U * (1 - z)` with random a priori ultimate `U`
and random cumulative development proportion `z`. -/
def bfStochasticReserveEstimate (U z : Omega -> Real) : Omega -> Real :=
  fun omega => U omega * (1 - z omega)

/-- The exact variance formula for a product of independent random variables.
The product square-integrability assumption is stated explicitly. -/
theorem variance_mul_of_indepFun [IsProbabilityMeasure mu]
    (X Y : Omega -> Real) (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu)
    (hXY : MemLp (X * Y) 2 mu) (hindep : X ⟂ᵢ[mu] Y) :
    variance (X * Y) mu =
      (integral mu X) ^ 2 * variance Y mu +
        variance X mu * variance Y mu +
        variance X mu * (integral mu Y) ^ 2 := by
  have hmean : integral mu (X * Y) = integral mu X * integral mu Y :=
    hindep.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
  have hindepSq : (fun omega => X omega ^ 2) ⟂ᵢ[mu] (fun omega => Y omega ^ 2) := by
    change ((fun x : Real => x ^ 2) ∘ X) ⟂ᵢ[mu] ((fun y : Real => y ^ 2) ∘ Y)
    exact hindep.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hsq : integral mu (fun omega => (X omega * Y omega) ^ 2) =
      integral mu (fun omega => X omega ^ 2) * integral mu (fun omega => Y omega ^ 2) := by
    have h := hindepSq.integral_mul_eq_mul_integral
      hX.integrable_sq.aestronglyMeasurable hY.integrable_sq.aestronglyMeasurable
    simpa only [Pi.mul_apply, mul_pow] using h
  rw [variance_eq_sub hXY]
  change integral mu (fun omega => (X omega * Y omega) ^ 2) -
    (integral mu (X * Y)) ^ 2 = _
  rw [hsq, hmean]
  have hx := variance_eq_sub hX
  have hy := variance_eq_sub hY
  simp only [Pi.pow_apply] at hx hy
  have hx' : integral mu (fun omega => X omega ^ 2) =
      variance X mu + (integral mu X) ^ 2 := by
    linarith
  have hy' : integral mu (fun omega => Y omega ^ 2) =
      variance Y mu + (integral mu Y) ^ 2 := by
    linarith
  rw [hx', hy']
  ring

/-- Mack (2008), pp. 95-96: exact estimation variance of the stochastic BF
reserve when the selected prior and development proportion are independent. -/
theorem variance_bfStochasticReserveEstimate [IsProbabilityMeasure mu]
    (U z : Omega -> Real) (hU : MemLp U 2 mu) (hz : MemLp z 2 mu)
    (hR : MemLp (bfStochasticReserveEstimate U z) 2 mu)
    (hindep : U ⟂ᵢ[mu] z) :
    variance (bfStochasticReserveEstimate U z) mu =
      ((integral mu U) ^ 2 + variance U mu) * variance z mu +
        variance U mu * (1 - integral mu z) ^ 2 := by
  let q : Omega -> Real := fun omega => 1 - z omega
  have hq : MemLp q 2 mu := (memLp_const 1).sub hz
  have hiq : U ⟂ᵢ[mu] q := by
    simpa [Function.comp_def] using
      hindep.comp measurable_id (measurable_const.sub measurable_id)
  have hprod : U * q = bfStochasticReserveEstimate U z := by
    ext omega
    rfl
  have hv := variance_mul_of_indepFun U q hU hq (hprod.symm ▸ hR) hiq
  rw [hprod] at hv
  rw [hv, variance_const_sub hz.aestronglyMeasurable 1]
  have hqmean : integral mu q = 1 - integral mu z := by
    rw [integral_sub (integrable_const 1) (hz.integrable one_le_two), integral_const,
      probReal_univ, one_smul]
  rw [hqmean]
  ring

/-- Unconditional mean squared prediction error. Mack's displayed MSEP is
conditional on the observed increments; common independence from those data
reduces it to this unconditional quantity. -/
def bfMeanSquaredPredictionError (mu : Measure Omega)
    (prediction target : Omega -> Real) : Real :=
  integral mu fun omega => (prediction omega - target omega) ^ 2

/-- Exact single-row MSEP decomposition. If prediction and target are
independent and unbiased for the same mean, MSEP is estimation variance plus
process variance. -/
theorem bfMeanSquaredPredictionError_eq_variance_add [IsProbabilityMeasure mu]
    (prediction target : Omega -> Real)
    (hprediction : MemLp prediction 2 mu) (htarget : MemLp target 2 mu)
    (hindep : prediction ⟂ᵢ[mu] target)
    (hunbiased : integral mu prediction = integral mu target) :
    bfMeanSquaredPredictionError mu prediction target =
      variance prediction mu + variance target mu := by
  have hmean : integral mu (prediction - target) = 0 := by
    change (integral mu fun omega => prediction omega - target omega) = 0
    rw [integral_sub (hprediction.integrable one_le_two) (htarget.integrable one_le_two),
      hunbiased, sub_self]
  have hcenter := variance_eq_integral (hprediction.sub htarget).aemeasurable
  have hvar := variance_sub hprediction htarget
  rw [hindep.covariance_eq_zero hprediction htarget] at hvar
  unfold bfMeanSquaredPredictionError
  have hfun : (fun omega => (prediction omega - target omega) ^ 2) =
      fun omega => ((prediction - target) omega - integral mu (prediction - target)) ^ 2 := by
    funext omega
    simp [hmean]
  rw [hfun, ← hcenter, hvar]
  ring

/-- Mack's single-row prediction-error decomposition with BF3 substituted.
The estimate and the future reserve are required to be independent and to
have the same mean. BF1 and BF3 then identify the process component as the
volume times the sum of the future column variances. -/
theorem bfMeanSquaredPredictionError_eq [IsProbabilityMeasure mu]
    (X : RandomTriangle Omega n) (x sigma2 : Nat -> Real)
    (prediction : Omega -> Real) (i d m : Nat)
    (hi : i < n) (hprediction : MemLp prediction 2 mu)
    (hinc : forall k, k ∈ Ico d m -> MemLp (X.bfIncrementRv i k) 2 mu)
    (hindepIncrements : BFFullIncrementIndependence X mu)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hindepPrediction : prediction ⟂ᵢ[mu] X.bfFutureReserveRv i d m)
    (hunbiased : integral mu prediction = integral mu (X.bfFutureReserveRv i d m)) :
    bfMeanSquaredPredictionError mu prediction (X.bfFutureReserveRv i d m) =
      variance prediction mu + x i * Finset.sum (Ico d m) sigma2 := by
  have hfuture : MemLp (X.bfFutureReserveRv i d m) 2 mu := by
    rw [RandomTriangle.bfFutureReserveRv]
    exact memLp_finsetSum' (Ico d m) hinc
  rw [bfMeanSquaredPredictionError_eq_variance_add prediction
    (X.bfFutureReserveRv i d m) hprediction hfuture hindepPrediction hunbiased]
  rw [variance_bfFutureReserveRv X x sigma2 i d m hi hindepIncrements hvar hinc]

/-- Mack's common-independence assumption on page 95: the pair consisting of
the BF estimate and the future reserve is independent of the observed-data
sigma-algebra. -/
def BFObservedPredictionIndependence (mu : Measure Omega) (G : MeasurableSpace Omega)
    (prediction target : Omega -> Real) : Prop :=
  Indep (MeasurableSpace.comap (fun omega => (prediction omega, target omega)) inferInstance)
    G mu

/-- Conditional form of Mack's single-row prediction-error calculation. Common
independence from the observed data makes the conditional squared error equal
to its unconditional mean; the preceding theorem evaluates that mean as
estimation variance plus the BF3 process variance. -/
theorem condExp_sq_bfPredictionError_eq [IsProbabilityMeasure mu]
    (X : RandomTriangle Omega n) (x sigma2 : Nat -> Real)
    (prediction : Omega -> Real) (i d m : Nat)
    (hG : G <= ‹MeasurableSpace Omega›) (hi : i < n)
    (hprediction : MemLp prediction 2 mu)
    (hinc : forall k, k ∈ Ico d m -> MemLp (X.bfIncrementRv i k) 2 mu)
    (hindepIncrements : BFFullIncrementIndependence X mu)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hindepPrediction : prediction ⟂ᵢ[mu] X.bfFutureReserveRv i d m)
    (hunbiased : integral mu prediction = integral mu (X.bfFutureReserveRv i d m))
    (hpairMeas : Measurable fun omega =>
      (prediction omega, X.bfFutureReserveRv i d m omega))
    (hobs : BFObservedPredictionIndependence mu G prediction
      (X.bfFutureReserveRv i d m)) :
    mu[fun omega =>
      (prediction omega - X.bfFutureReserveRv i d m omega) ^ 2 | G] =ᵐ[mu]
      fun _ => variance prediction mu + x i * Finset.sum (Ico d m) sigma2 := by
  let pair : Omega -> Real × Real := fun omega =>
    (prediction omega, X.bfFutureReserveRv i d m omega)
  let sqDiff : Real × Real -> Real := fun p => (p.1 - p.2) ^ 2
  have herr : StronglyMeasurable[MeasurableSpace.comap pair inferInstance]
      (fun omega => (prediction omega - X.bfFutureReserveRv i d m omega) ^ 2) := by
    change StronglyMeasurable[MeasurableSpace.comap pair inferInstance] (sqDiff ∘ pair)
    exact (((measurable_fst.sub measurable_snd).pow_const 2).comp
      (comap_measurable pair)).stronglyMeasurable
  have hcond := condExp_indep_eq hpairMeas.comap_le hG herr hobs
  have hvalue := bfMeanSquaredPredictionError_eq X x sigma2 prediction i d m hi
    hprediction hinc hindepIncrements hvar hindepPrediction hunbiased
  rw [show integral mu (fun omega =>
      (prediction omega - X.bfFutureReserveRv i d m omega) ^ 2) =
      bfMeanSquaredPredictionError mu prediction (X.bfFutureReserveRv i d m) by rfl,
    hvalue] at hcond
  exact hcond

/-! ## Practical estimators and assessments from Sections 4-5 -/

/-- The raw estimator of one development proportion when the volumes `x_i`
are known, Mack (2008), equations (1) and (3), on an explicit finite set of
accident years. -/
def RandomTriangle.bfYRawRv (X : RandomTriangle Omega n) (x : Nat -> Real)
    (s : Finset Nat) (k : Nat) : Omega -> Real :=
  fun omega => (Finset.sum s fun i => X.bfIncrementRv i k omega) / Finset.sum s x

/-- The raw development-proportion estimator is unbiased under BF2 when its
volume denominator is nonzero. This is the unbiased part of Mack's statement
following equation (1); no best-linear claim is made here. -/
theorem integral_bfYRawRv [IsProbabilityMeasure mu]
    (X : RandomTriangle Omega n) (x y : Nat -> Real) (s : Finset Nat) (k m : Nat)
    (hk : k < m) (hrows : forall i, i ∈ s -> i < n)
    (hmean : BFIncrementMean X mu x y m)
    (hint : forall i, i ∈ s -> Integrable (X.bfIncrementRv i k) mu)
    (hden : Finset.sum s x ≠ 0) :
    integral mu (X.bfYRawRv x s k) = y k := by
  unfold RandomTriangle.bfYRawRv
  rw [integral_div]
  rw [integral_finsetSum s hint]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hmean i (hrows i hi) k hk]]
  rw [← Finset.sum_mul]
  field_simp

/-- Exact variance of the raw development-proportion estimator under BF1 and
BF3. This is the equality behind Mack's equation (6) before a smoothed selected
pattern is substituted for the raw estimator. -/
theorem variance_bfYRawRv
    (X : RandomTriangle Omega n) (x sigma2 : Nat -> Real)
    (s : Finset Nat) (k m : Nat) (hk : k < m)
    (hrows : forall i, i ∈ s -> i < n)
    (hindep : BFFullIncrementIndependence X mu)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hmem : forall i, i ∈ s -> MemLp (X.bfIncrementRv i k) 2 mu)
    (hden : Finset.sum s x ≠ 0) :
    variance (X.bfYRawRv x s k) mu = sigma2 k / Finset.sum s x := by
  let total : Omega -> Real := Finset.sum s fun i => X.bfIncrementRv i k
  have hpair : Set.Pairwise (↑s : Set Nat) fun i j =>
      X.bfIncrementRv i k ⟂ᵢ[mu] X.bfIncrementRv j k := by
    intro i hi j hj hij
    have hp : (i, k) ≠ (j, k) := by
      intro hpairs
      exact hij (Prod.mk.inj hpairs).1
    unfold BFFullIncrementIndependence at hindep
    exact hindep.indepFun hp
  have htotal : variance total mu = Finset.sum s fun i =>
      variance (X.bfIncrementRv i k) mu := by
    exact IndepFun.variance_sum hmem hpair
  have htotalValue : variance total mu = Finset.sum s x * sigma2 k := by
    rw [htotal]
    rw [Finset.sum_congr rfl fun i hi => hvar i (hrows i hi) k hk]
    rw [Finset.sum_mul]
  have hpoint : X.bfYRawRv x s k = fun omega => total omega / Finset.sum s x := by
    funext omega
    simp [RandomTriangle.bfYRawRv, total, Finset.sum_apply]
  rw [hpoint]
  change variance (fun omega => total omega * (Finset.sum s x)⁻¹) mu = _
  rw [variance_mul_const, htotalValue]
  field_simp

/-! ### Mack's equations (1) and (2) -/

/-- A linear estimator of one development proportion on a finite set of
accident years. -/
def RandomTriangle.bfLinearPatternRv (X : RandomTriangle Omega n)
    (coefficient : Nat -> Real) (s : Finset Nat) (k : Nat) : Omega -> Real :=
  fun omega => Finset.sum s fun i => coefficient i * X.bfIncrementRv i k omega

/-- Under BF2, a linear estimator has mean `y k * sum_i coefficient_i x_i`. -/
theorem integral_bfLinearPatternRv [IsProbabilityMeasure mu]
    (X : RandomTriangle Omega n) (x y coefficient : Nat -> Real)
    (s : Finset Nat) (k m : Nat) (hk : k < m)
    (hrows : forall i, i ∈ s -> i < n)
    (hmean : BFIncrementMean X mu x y m)
    (hint : forall i, i ∈ s -> Integrable (X.bfIncrementRv i k) mu) :
    integral mu (X.bfLinearPatternRv coefficient s k) =
      y k * Finset.sum s fun i => coefficient i * x i := by
  unfold RandomTriangle.bfLinearPatternRv
  rw [integral_finsetSum s fun i hi => (hint i hi).const_mul (coefficient i)]
  rw [Finset.sum_congr rfl fun i _ => integral_const_mul
    (μ := mu) (coefficient i) (X.bfIncrementRv i k)]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hmean i (hrows i hi) k hk]]
  rw [mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Under BF1 and BF3, the variance of a linear pattern estimator is its
diagonal quadratic form. -/
theorem variance_bfLinearPatternRv
    (X : RandomTriangle Omega n) (x sigma2 coefficient : Nat -> Real)
    (s : Finset Nat) (k m : Nat) (hk : k < m)
    (hrows : forall i, i ∈ s -> i < n)
    (hindep : BFFullIncrementIndependence X mu)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hmem : forall i, i ∈ s -> MemLp (X.bfIncrementRv i k) 2 mu) :
    variance (X.bfLinearPatternRv coefficient s k) mu =
      sigma2 k * Finset.sum s fun i => x i * coefficient i ^ 2 := by
  unfold RandomTriangle.bfLinearPatternRv
  have hpair : Set.Pairwise (↑s : Set Nat) fun i j =>
      (fun omega => coefficient i * X.bfIncrementRv i k omega) ⟂ᵢ[mu]
        fun omega => coefficient j * X.bfIncrementRv j k omega := by
    intro i hi j hj hij
    have hp : (i, k) ≠ (j, k) := by
      intro hpairs
      exact hij (Prod.mk.inj hpairs).1
    have hbase := hindep.indepFun hp
    simpa [Function.comp_def] using hbase.comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  rw [show (fun omega => Finset.sum s fun i => coefficient i * X.bfIncrementRv i k omega) =
      Finset.sum s fun i omega => coefficient i * X.bfIncrementRv i k omega by
    funext omega
    exact (Finset.sum_apply omega s fun i omega =>
      coefficient i * X.bfIncrementRv i k omega).symm]
  rw [IndepFun.variance_sum
    (fun i hi => (hmem i hi).const_mul (coefficient i)) hpair]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [variance_const_mul, hvar i (hrows i hi) k hk]]
  rw [mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Exact square-completion identity for the variance of an unbiased linear
pattern estimator. -/
theorem bfLinearPatternRisk_sub_raw
    (x coefficient : Nat -> Real) (sigma : Real) (s : Finset Nat)
    (hden : Finset.sum s x ≠ 0)
    (hunbiased : Finset.sum s (fun i => coefficient i * x i) = 1) :
    sigma * Finset.sum s (fun i => x i * coefficient i ^ 2) -
        sigma / Finset.sum s x =
      sigma * Finset.sum s (fun i =>
        x i * (coefficient i - 1 / Finset.sum s x) ^ 2) := by
  have hexpand :
      Finset.sum s (fun i => x i *
          (coefficient i - 1 / Finset.sum s x) ^ 2) =
        Finset.sum s (fun i => x i * coefficient i ^ 2) -
          2 * (1 / Finset.sum s x) *
            Finset.sum s (fun i => coefficient i * x i) +
          (1 / Finset.sum s x) ^ 2 * Finset.sum s x := by
    calc
      Finset.sum s (fun i => x i *
          (coefficient i - 1 / Finset.sum s x) ^ 2) =
          Finset.sum s (fun i =>
            x i * coefficient i ^ 2 -
              2 * (1 / Finset.sum s x) * (coefficient i * x i) +
              (1 / Finset.sum s x) ^ 2 * x i) := by
            exact Finset.sum_congr rfl fun i _ => by ring
      _ = Finset.sum s (fun i => x i * coefficient i ^ 2) -
          2 * (1 / Finset.sum s x) *
            Finset.sum s (fun i => coefficient i * x i) +
          (1 / Finset.sum s x) ^ 2 * Finset.sum s x := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sum, mul_sum]
  rw [hexpand, hunbiased]
  field_simp [hden]
  ring

/-- **Mack (2008), equation (1).** The raw estimator is best among linear
unbiased estimators under BF1--BF3. The conclusion records both unbiasedness
and the variance comparison. -/
theorem bfYRawRv_best_linear_unbiased [IsProbabilityMeasure mu]
    (X : RandomTriangle Omega n) (x y sigma2 coefficient : Nat -> Real)
    (s : Finset Nat) (k m : Nat) (hk : k < m)
    (hrows : forall i, i ∈ s -> i < n)
    (hindep : BFFullIncrementIndependence X mu)
    (hmean : BFIncrementMean X mu x y m)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hmem : forall i, i ∈ s -> MemLp (X.bfIncrementRv i k) 2 mu)
    (hx : forall i, i ∈ s -> 0 <= x i) (hsigma : 0 <= sigma2 k)
    (hden : Finset.sum s x ≠ 0)
    (hunbiased : Finset.sum s (fun i => coefficient i * x i) = 1) :
    integral mu (X.bfYRawRv x s k) = y k ∧
      integral mu (X.bfLinearPatternRv coefficient s k) = y k ∧
      variance (X.bfYRawRv x s k) mu <=
        variance (X.bfLinearPatternRv coefficient s k) mu := by
  have hrawMean := integral_bfYRawRv X x y s k m hk hrows hmean
    (fun i hi => (hmem i hi).integrable one_le_two) hden
  have hlinearMean := integral_bfLinearPatternRv X x y coefficient s k m hk hrows hmean
    (fun i hi => (hmem i hi).integrable one_le_two)
  have hrawVar := variance_bfYRawRv X x sigma2 s k m hk hrows hindep hvar hmem hden
  have hlinearVar := variance_bfLinearPatternRv X x sigma2 coefficient s k m hk hrows
    hindep hvar hmem
  refine ⟨hrawMean, ?_, ?_⟩
  · rw [hlinearMean, hunbiased, mul_one]
  · rw [hrawVar, hlinearVar]
    have hid := bfLinearPatternRisk_sub_raw x coefficient (sigma2 k) s hden hunbiased
    have hnonneg : 0 <= sigma2 k * Finset.sum s (fun i =>
        x i * (coefficient i - 1 / Finset.sum s x) ^ 2) := by
      exact mul_nonneg hsigma (Finset.sum_nonneg fun i hi =>
        mul_nonneg (hx i hi) (sq_nonneg _))
    linarith

/-- Weighted residual sum of squares around the raw development-proportion
estimator. -/
def RandomTriangle.bfResidualSumSqRv (X : RandomTriangle Omega n)
    (x : Nat -> Real) (s : Finset Nat) (k : Nat) : Omega -> Real :=
  fun omega => Finset.sum s fun i =>
    (X.bfIncrementRv i k omega - x i * X.bfYRawRv x s k omega) ^ 2 / x i

/-- The residual variance estimator of Mack (2008), equation (2), on an
explicit finite set of accident years. -/
def RandomTriangle.bfSigma2RawOnRv (X : RandomTriangle Omega n)
    (x : Nat -> Real) (s : Finset Nat) (k : Nat) : Omega -> Real :=
  fun omega => (1 / ((s.card : Real) - 1)) * X.bfResidualSumSqRv x s k omega

/-- Deterministic residual sum-of-squares identity behind equation (2). -/
theorem bf_raw_weighted_sq_dev
    (claim x : Nat -> Real) (s : Finset Nat) (y : Real)
    (hx : forall i, i ∈ s -> x i ≠ 0) (hden : Finset.sum s x ≠ 0) :
    Finset.sum s (fun i =>
        (claim i - x i * (Finset.sum s claim / Finset.sum s x)) ^ 2 / x i) =
      Finset.sum s (fun i => (claim i - x i * y) ^ 2 / x i) -
        Finset.sum s x * (Finset.sum s claim / Finset.sum s x - y) ^ 2 := by
  have hexpand : forall center : Real,
      Finset.sum s (fun i => (claim i - x i * center) ^ 2 / x i) =
        Finset.sum s (fun i => claim i ^ 2 / x i) -
          2 * center * Finset.sum s claim + center ^ 2 * Finset.sum s x := by
    intro center
    calc
      Finset.sum s (fun i => (claim i - x i * center) ^ 2 / x i) =
          Finset.sum s (fun i =>
            claim i ^ 2 / x i - 2 * center * claim i + center ^ 2 * x i) := by
            exact Finset.sum_congr rfl fun i hi => by
              field_simp [hx i hi]
              ring
      _ = Finset.sum s (fun i => claim i ^ 2 / x i) -
          2 * center * Finset.sum s claim + center ^ 2 * Finset.sum s x := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sum, mul_sum]
  rw [hexpand, hexpand]
  field_simp [hden]
  ring

/-- The residual sum of squares equals the true-centre sum minus the one
degree of freedom spent estimating the development proportion. -/
theorem RandomTriangle.bfResidualSumSqRv_eq
    (X : RandomTriangle Omega n) (x : Nat -> Real) (s : Finset Nat)
    (k : Nat) (y : Real)
    (hx : forall i, i ∈ s -> x i ≠ 0) (hden : Finset.sum s x ≠ 0) :
    X.bfResidualSumSqRv x s k = fun omega =>
      Finset.sum s (fun i =>
        (X.bfIncrementRv i k omega - x i * y) ^ 2 / x i) -
      Finset.sum s x * (X.bfYRawRv x s k omega - y) ^ 2 := by
  funext omega
  simpa [RandomTriangle.bfResidualSumSqRv, RandomTriangle.bfYRawRv] using
    bf_raw_weighted_sq_dev (fun i => X.bfIncrementRv i k omega) x s y hx hden

/-- **Mack (2008), equation (2).** With at least two contributing accident
years, the raw residual variance estimator is unbiased for `sigma2 k` under
BF1--BF3. -/
theorem integral_bfSigma2RawOnRv [IsProbabilityMeasure mu]
    (X : RandomTriangle Omega n) (x y sigma2 : Nat -> Real)
    (s : Finset Nat) (k m : Nat) (hk : k < m) (hcard : 2 <= s.card)
    (hrows : forall i, i ∈ s -> i < n)
    (hindep : BFFullIncrementIndependence X mu)
    (hmean : BFIncrementMean X mu x y m)
    (hvar : BFIncrementVariance X mu x sigma2 m)
    (hmem : forall i, i ∈ s -> MemLp (X.bfIncrementRv i k) 2 mu)
    (hx : forall i, i ∈ s -> x i ≠ 0)
    (hden : Finset.sum s x ≠ 0) :
    integral mu (X.bfSigma2RawOnRv x s k) = sigma2 k := by
  let yhat : Omega -> Real := X.bfYRawRv x s k
  let A : Omega -> Real := fun omega => Finset.sum s fun i =>
    (X.bfIncrementRv i k omega - x i * y k) ^ 2 / x i
  let B : Omega -> Real := fun omega =>
    Finset.sum s x * (yhat omega - y k) ^ 2
  have hyhatMem : MemLp yhat 2 mu := by
    have hsum : MemLp (fun omega => Finset.sum s fun i =>
        X.bfIncrementRv i k omega) 2 mu := memLp_finsetSum s hmem
    have hpoint : yhat = fun omega =>
        (Finset.sum s fun i => X.bfIncrementRv i k omega) *
          (Finset.sum s x)⁻¹ := by
      funext omega
      simp [yhat, RandomTriangle.bfYRawRv, div_eq_mul_inv]
    rw [hpoint]
    exact hsum.mul_const _
  have htermMem : forall i, i ∈ s ->
      MemLp (fun omega => X.bfIncrementRv i k omega - x i * y k) 2 mu := by
    intro i hi
    exact (hmem i hi).sub (memLp_const (x i * y k))
  have htermInt : forall i, i ∈ s -> Integrable
      (fun omega => (X.bfIncrementRv i k omega - x i * y k) ^ 2 / x i) mu := by
    intro i hi
    exact ((htermMem i hi).integrable_sq).div_const (x i)
  have hAint : Integrable A mu := by
    exact (integrable_finsetSum s htermInt).congr
      (Eventually.of_forall fun omega => by simp [A])
  have hBint : Integrable B mu := by
    exact ((hyhatMem.sub (memLp_const (y k))).integrable_sq.const_mul
      (Finset.sum s x)).congr (Eventually.of_forall fun omega => by simp [B, yhat])
  have htermValue : forall i, i ∈ s -> integral mu
      (fun omega => (X.bfIncrementRv i k omega - x i * y k) ^ 2 / x i) =
      sigma2 k := by
    intro i hi
    have hcenter : integral mu
        (fun omega => (X.bfIncrementRv i k omega - x i * y k) ^ 2) =
        variance (X.bfIncrementRv i k) mu := by
      have hv := variance_eq_integral (hmem i hi).aemeasurable
      rw [hmean i (hrows i hi) k hk] at hv
      exact hv.symm
    calc
      integral mu
          (fun omega => (X.bfIncrementRv i k omega - x i * y k) ^ 2 / x i) =
          integral mu
            (fun omega => (X.bfIncrementRv i k omega - x i * y k) ^ 2) / x i :=
        integral_div (x i) _
      _ = variance (X.bfIncrementRv i k) mu / x i := by rw [hcenter]
      _ = sigma2 k := by rw [hvar i (hrows i hi) k hk]; field_simp [hx i hi]
  have hAvalue : integral mu A = (s.card : Real) * sigma2 k := by
    have hApoint : A = fun omega => Finset.sum s fun i =>
        (X.bfIncrementRv i k omega - x i * y k) ^ 2 / x i := rfl
    rw [hApoint, integral_finsetSum s htermInt]
    calc
      (Finset.sum s fun i => integral mu
          (fun omega => (X.bfIncrementRv i k omega - x i * y k) ^ 2 / x i)) =
          Finset.sum s (fun _ => sigma2 k) :=
        Finset.sum_congr rfl fun i hi => htermValue i hi
      _ = (s.card : Real) * sigma2 k := by rw [Finset.sum_const, nsmul_eq_mul]
  have hyhatMean : integral mu yhat = y k := by
    exact integral_bfYRawRv X x y s k m hk hrows hmean
      (fun i hi => (hmem i hi).integrable one_le_two) hden
  have hyhatVar : variance yhat mu = sigma2 k / Finset.sum s x := by
    exact variance_bfYRawRv X x sigma2 s k m hk hrows hindep hvar hmem hden
  have hcenterY : integral mu (fun omega => (yhat omega - y k) ^ 2) =
      sigma2 k / Finset.sum s x := by
    have hv := variance_eq_integral hyhatMem.aemeasurable
    rw [hyhatMean] at hv
    exact hv ▸ hyhatVar
  have hBvalue : integral mu B = sigma2 k := by
    have hBpoint : B = fun omega =>
        Finset.sum s x * (yhat omega - y k) ^ 2 := rfl
    rw [hBpoint, integral_const_mul, hcenterY]
    field_simp [hden]
  have hresidual : integral mu (X.bfResidualSumSqRv x s k) =
      ((s.card : Real) - 1) * sigma2 k := by
    rw [X.bfResidualSumSqRv_eq x s k (y k) hx hden]
    rw [integral_sub hAint hBint, hAvalue, hBvalue]
    ring
  have hcardReal : (1 : Real) < (s.card : Real) := by
    exact_mod_cast (show 1 < s.card by omega)
  have hdof : (s.card : Real) - 1 ≠ 0 := by positivity
  unfold RandomTriangle.bfSigma2RawOnRv
  rw [integral_const_mul, hresidual]
  field_simp [hdof]

/-- Raw development-proportion estimate, Mack (2008), equation (3).

The arguments `n` and `k` retain the source's one-based symbols here, so the
contributing rows are `range (n + 1 - k)`. For the repository's zero-based
triangle convention, use `RandomTriangle.bfYRawRv` with an explicit set such
as `obsCol n k`. -/
def bfYRaw (S : Nat -> Nat -> Real) (U : Nat -> Real) (n k : Nat) : Real :=
  (Finset.sum (range (n + 1 - k)) fun i => S i k) /
    Finset.sum (range (n + 1 - k)) U

/-- Raw column variance estimate after a selected pattern, Mack (2008),
equation (4). It is a definition because the selected pattern may include
manual smoothing and tail extrapolation. Its `n` and `k` arguments retain the
source's one-based symbols, as in `bfYRaw`. -/
def bfSigma2Raw (S : Nat -> Nat -> Real) (U y : Nat -> Real) (n k : Nat) : Real :=
  (1 / (n - k : Real)) *
    Finset.sum (range (n + 1 - k)) fun i => (S i k - U i * y k) ^ 2 / U i

/-- Assessed squared standard error of a selected development proportion,
Mack (2008), equation (6). Its `n` and `k` arguments retain the source's
one-based symbols, as in `bfYRaw`. -/
def bfYStdErrSq (U sigma2 : Nat -> Real) (n k : Nat) : Real :=
  sigma2 k / Finset.sum (range (n + 1 - k)) U

/-- Mack's equation (7): the assessed variance of a cumulative pattern is the
minimum of the sums of development-proportion variances on its two sides. -/
def bfZStdErrSq (yStdErrSq : Nat -> Real) (m k : Nat) : Real :=
  min (Finset.sum (range k) yStdErrSq) (Finset.sum (Ico k m) yStdErrSq)

/-- Plug-in estimate of the future process variance on one accident year. -/
def bfProcessErrorEstimate (U sigma2 : Nat -> Real) (i d m : Nat) : Real :=
  U i * Finset.sum (Ico d m) sigma2

/-- Mack's pure estimation-error assessment for one BF reserve, pp. 97-98. -/
def bfEstimationErrorEstimate (U uStdErrSq z zStdErrSq : Real) : Real :=
  (U ^ 2 + uStdErrSq) * zStdErrSq + uStdErrSq * (1 - z) ^ 2

/-- Mack's single-year prediction-error estimate, p. 97: process error plus
the assessed estimation error. -/
def bfMsepEstimate (process U uStdErrSq z zStdErrSq : Real) : Real :=
  process + bfEstimationErrorEstimate U uStdErrSq z zStdErrSq

/-- The prediction-error estimate is exactly its named process and estimation
components. -/
theorem bfMsepEstimate_eq (process U uStdErrSq z zStdErrSq : Real) :
    bfMsepEstimate process U uStdErrSq z zStdErrSq =
      process + (U ^ 2 + uStdErrSq) * zStdErrSq + uStdErrSq * (1 - z) ^ 2 := by
  unfold bfMsepEstimate bfEstimationErrorEstimate
  ring

/-- Exact product-covariance identity used by Mack for total-reserve
estimation error before he drops the middle, second-order term. -/
theorem covariance_mul_mul_of_pair_indep [IsProbabilityMeasure mu]
    (X W Y Z : Omega -> Real)
    (hX : MemLp X 2 mu) (hW : MemLp W 2 mu)
    (hY : MemLp Y 2 mu) (hZ : MemLp Z 2 mu)
    (hXY : MemLp (X * Y) 2 mu) (hWZ : MemLp (W * Z) 2 mu)
    (hXW : Integrable (X * W) mu) (hYZ : Integrable (Y * Z) mu)
    (hindep : (fun omega => (X omega, W omega)) ⟂ᵢ[mu]
      fun omega => (Y omega, Z omega)) :
    covariance (X * Y) (W * Z) mu =
      covariance X W mu * integral mu Y * integral mu Z +
        covariance X W mu * covariance Y Z mu +
        integral mu X * integral mu W * covariance Y Z mu := by
  have hXmY : X ⟂ᵢ[mu] Y := by
    simpa [Function.comp_def] using hindep.comp measurable_fst measurable_fst
  have hWmZ : W ⟂ᵢ[mu] Z := by
    simpa [Function.comp_def] using hindep.comp measurable_snd measurable_snd
  have hPairProducts : (X * W) ⟂ᵢ[mu] (Y * Z) := by
    change (fun omega => X omega * W omega) ⟂ᵢ[mu]
      (fun omega => Y omega * Z omega)
    change ((fun p : Real × Real => p.1 * p.2) ∘ fun omega => (X omega, W omega)) ⟂ᵢ[mu]
      ((fun p : Real × Real => p.1 * p.2) ∘ fun omega => (Y omega, Z omega))
    exact hindep.comp (measurable_fst.mul measurable_snd) (measurable_fst.mul measurable_snd)
  have hJoint : integral mu (fun omega => (X omega * W omega) * (Y omega * Z omega)) =
      integral mu (X * W) * integral mu (Y * Z) := by
    have h := hPairProducts.integral_mul_eq_mul_integral
      hXW.aestronglyMeasurable hYZ.aestronglyMeasurable
    change (integral mu fun omega => (X omega * W omega) * (Y omega * Z omega)) =
      (integral mu fun omega => X omega * W omega) *
        integral mu (fun omega => Y omega * Z omega) at h
    change (integral mu fun omega => (X omega * W omega) * (Y omega * Z omega)) =
      (integral mu fun omega => X omega * W omega) *
        integral mu (fun omega => Y omega * Z omega)
    exact h
  rw [covariance_eq_sub hXY hWZ]
  rw [hXmY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable]
  rw [hWmZ.integral_mul_eq_mul_integral hW.aestronglyMeasurable hZ.aestronglyMeasurable]
  have hprod : integral mu ((X * Y) * (W * Z)) =
      integral mu (X * W) * integral mu (Y * Z) := by
    rw [show (X * Y) * (W * Z) = fun omega =>
        (X omega * W omega) * (Y omega * Z omega) by
      funext omega
      simp only [Pi.mul_apply]
      ring]
    exact hJoint
  rw [hprod]
  rw [covariance_eq_sub hX hW, covariance_eq_sub hY hZ]
  ring

/-- Mack's p. 99 covariance approximation after omitting the middle term in
the exact product-covariance identity. Correlations and standard errors are
inputs assessed outside this definition. -/
def bfCovarianceApprox (rhoU rhoZ seUi seUj seZi seZj Ui Uj zi zj : Real) : Real :=
  rhoU * seUi * seUj * (1 - zi) * (1 - zj) +
    rhoZ * seZi * seZj * Ui * Uj

end

end VerifiedReserving
