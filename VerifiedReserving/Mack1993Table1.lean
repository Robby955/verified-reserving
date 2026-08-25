import VerifiedReserving.ChainLadder

/-!
# Kernel-checked arithmetic for Mack's 1993 example

This file transcribes the Taylor-Ashe cumulative run-off triangle printed in
Mack (1993), Section 4, Table 1. The exact rational calculations below produce
the development factors and estimable variance parameters printed beneath that
table, and the overall chain-ladder reserve printed in Table 2.

The paper prints rounded decimals. The Lean statements retain the exact
rational values computed from the integer triangle. The ninth variance value
printed by Mack is an extrapolation convention, not the `sigma2` estimator, and
is therefore not asserted as a theorem here.
-/

open Finset

namespace VerifiedReserving

noncomputable section

/-- The cumulative Taylor-Ashe triangle in Mack (1993), Table 1, p. 221.
Rows and columns are zero-based; unobserved cells are set to zero and are not
read by the estimators. -/
def taylorAshe : ℕ → ℕ → ℝ
  | 0, 0 => 357848 | 0, 1 => 1124788 | 0, 2 => 1735330 | 0, 3 => 2218270
  | 0, 4 => 2745596 | 0, 5 => 3319994 | 0, 6 => 3466336 | 0, 7 => 3606286
  | 0, 8 => 3833515 | 0, 9 => 3901463
  | 1, 0 => 352118 | 1, 1 => 1236139 | 1, 2 => 2170033 | 1, 3 => 3353322
  | 1, 4 => 3799067 | 1, 5 => 4120063 | 1, 6 => 4647867 | 1, 7 => 4914039
  | 1, 8 => 5339085
  | 2, 0 => 290507 | 2, 1 => 1292306 | 2, 2 => 2218525 | 2, 3 => 3235179
  | 2, 4 => 3985995 | 2, 5 => 4132918 | 2, 6 => 4628910 | 2, 7 => 4909315
  | 3, 0 => 310608 | 3, 1 => 1418858 | 3, 2 => 2195047 | 3, 3 => 3757447
  | 3, 4 => 4029929 | 3, 5 => 4381982 | 3, 6 => 4588268
  | 4, 0 => 443160 | 4, 1 => 1136350 | 4, 2 => 2128333 | 4, 3 => 2897821
  | 4, 4 => 3402672 | 4, 5 => 3873311
  | 5, 0 => 396132 | 5, 1 => 1333217 | 5, 2 => 2180715 | 5, 3 => 2985752
  | 5, 4 => 3691712
  | 6, 0 => 440832 | 6, 1 => 1288463 | 6, 2 => 2419861 | 6, 3 => 3483130
  | 7, 0 => 359480 | 7, 1 => 1421128 | 7, 2 => 2864498
  | 8, 0 => 376686 | 8, 1 => 1363294
  | 9, 0 => 344014
  | _, _ => 0

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₁ = 3.49`. -/
theorem taylorAshe_fhat_0 :
    fhat taylorAshe 10 0 = (11614543 : ℝ) / 3327371 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₂ = 1.75`. -/
theorem taylorAshe_fhat_1 :
    fhat taylorAshe 10 1 = (17912342 : ℝ) / 10251249 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₃ = 1.46`. -/
theorem taylorAshe_fhat_2 :
    fhat taylorAshe 10 2 = (7310307 : ℝ) / 5015948 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₄ = 1.174`. -/
theorem taylorAshe_fhat_3 :
    fhat taylorAshe 10 3 = (21654971 : ℝ) / 18447791 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₅ = 1.104`. -/
theorem taylorAshe_fhat_4 :
    fhat taylorAshe 10 4 = (19828268 : ℝ) / 17963259 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₆ = 1.086`. -/
theorem taylorAshe_fhat_5 :
    fhat taylorAshe 10 5 = (1925709 : ℝ) / 1772773 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₇ = 1.054`. -/
theorem taylorAshe_fhat_6 :
    fhat taylorAshe 10 6 = (13429640 : ℝ) / 12743113 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₈ = 1.077`. -/
theorem taylorAshe_fhat_7 :
    fhat taylorAshe 10 7 = (366904 : ℝ) / 340813 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the development-factor display following Mack (1993),
equation (1), p. 214, applied to Table 1, p. 221; printed `fhat₉ = 1.018`. -/
theorem taylorAshe_fhat_8 :
    fhat taylorAshe 10 8 = (3901463 : ℝ) / 3833515 := by
  norm_num [fhat, T, S, contributors, sum_range_succ, taylorAshe]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₁² / 1000 = 160`. -/
theorem taylorAshe_sigma2_0 :
    sigma2 taylorAshe 10 0 =
      (273788502349135995859016546377758771756482157433 : ℝ) /
        1708185319140104307559030827166399071866880 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_0]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₂² / 1000 = 37.7`. -/
theorem taylorAshe_sigma2_1 :
    sigma2 taylorAshe 10 1 =
      (89808189938804297823708371158707459867715850937303182401 : ℝ) /
        2379853589404308386083834345102719300552508470596925 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_1]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₃² / 1000 = 42.0`. -/
theorem taylorAshe_sigma2_2 :
    sigma2 taylorAshe 10 2 =
      (5202465122855037249337087686409646412047001602727659161 : ℝ) /
        123970897531128060463598039143822825988886010739400 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_2]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₄² / 1000 = 15.2`. -/
theorem taylorAshe_sigma2_3 :
    sigma2 taylorAshe 10 3 =
      (12590305564039922065117691503861829099683820803 : ℝ) /
        829242327938718719943112566475637479117050 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_3]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₅² / 1000 = 13.7`. -/
theorem taylorAshe_sigma2_4 :
    sigma2 taylorAshe 10 4 =
      (4187912532241197921763811164947179043871 : ℝ) /
        304989712950224511469069981895680320 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_4]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₆² / 1000 = 8.19`. -/
theorem taylorAshe_sigma2_5 :
    sigma2 taylorAshe 10 5 =
      (1348070340928146967968855087248032472 : ℝ) /
        164684577521423688222977029019121 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_5]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₇² / 1000 = 0.447`. -/
theorem taylorAshe_sigma2_6 :
    sigma2 taylorAshe 10 6 =
      (7073953210983867309930020447 : ℝ) /
        15838985835422487097376016 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_6]

/-- Exact value from the variance-estimator display following Mack (1993),
equation (3), p. 217, applied to Table 1, p. 221; printed
`sigmahat₈² / 1000 = 1.15`. -/
theorem taylorAshe_sigma2_7 :
    sigma2 taylorAshe 10 7 =
      (2309913018750997506675 : ℝ) / 2013231246447440734 := by
  norm_num [sigma2, F, contributors, sum_range_succ, taylorAshe, taylorAshe_fhat_7]

/-- The sum of the ten chain-ladder reserves computed from Mack (1993),
Table 1, p. 221, using the reserve definition preceding Table 2 on that page. -/
def taylorAsheTotalReserve : ℝ :=
  ∑ i ∈ range 10, reserve taylorAshe 10 i

/-- The exact total reserve from Table 1 lies in the rounding interval for the
`18,681` thousand printed in Mack (1993), Table 2, p. 221. -/
theorem taylorAshe_total_reserve_rounds :
    (18680500 : ℝ) < taylorAsheTotalReserve ∧
      taylorAsheTotalReserve < 18681500 := by
  norm_num [taylorAsheTotalReserve, reserve, ultimate, Chat, sum_range_succ,
    prod_range_succ, prod_Ico_succ_top, taylorAshe,
    taylorAshe_fhat_0, taylorAshe_fhat_1, taylorAshe_fhat_2,
    taylorAshe_fhat_3, taylorAshe_fhat_4, taylorAshe_fhat_5,
    taylorAshe_fhat_6, taylorAshe_fhat_7, taylorAshe_fhat_8]

end

end VerifiedReserving
