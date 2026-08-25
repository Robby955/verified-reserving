# RAA case study: formalized Mack chain-ladder versus R ChainLadder

Verdict: the Python transcription of the formalized definitions reproduces `MackChainLadder(RAA, est.sigma = "Mack")` to printed precision in every cell (largest per-year gap 0.46 against integer-printed values, totals within 0.002 against two-decimal values), and with the last sigma swapped to the package's log-linear rule it also reproduces the package default total Mack S.E. 26,880.74. The conditional-resampling estimation-error term exceeds Mack's on RAA by 0.78 percent of the estimation-error part of the total MSEP and 0.11 percent of the total MSEP; the total standard error moves from 26,909 to 26,924.

Data and sources: `raa_cumulative.csv` (built by `build_raa_csv.py`), `SOURCES.md`, `published_r_chainladder.json`. Script: `raa_case_study.py`. Full printed output: `run_output.txt`. Machine-readable results: `raa_case_study_results.json`.

## 1. Inputs

The RAA triangle (Reinsurance Association of America, Historical Loss Development Study 1991, Automatic Facultative General Liability, cumulative incurred in $1000, accident years 1981 to 1990). Three public copies (chainladder-python `raa.csv`, the R ChainLadder vignette, and Mack 1994 p. 126) agree on all 55 cells; the CSV in this directory is generated from the first and checked against the other two by `build_raa_csv.py`.

The published comparison column is the R ChainLadder vignette output of `MackChainLadder(RAA, est.sigma = "Mack")`. Mack (1994) p. 130 prints the same table digit for digit, so the R output and Mack's own 1994 calculation are one and the same target.

Our column is `mack()` from `../reproduce_mack1993.py`, the Python transcription of the Lean definitions (volume-weighted f_k, Mack's sigma_k^2 with n-k-2 degrees of freedom, Mack's min-rule for the last sigma^2, Mack's per-year MSEP, and the total MSEP with Mack's cross terms). The case study script imports that function unchanged and asserts, bit for bit, that its own factored helper (used only to swap the last-sigma rule) returns the same numbers.

## 2. Development factors and variance parameters

| k | f_k (ours) | f_k (Mack 1994) | sigma_k^2 (ours) | alpha_k^2 (Mack 1994) |
|---|---|---|---|---|
| 1 | 2.999 | 2.999 | 27,883 | 27883 |
| 2 | 1.624 | 1.624 | 1,109 | 1109 |
| 3 | 1.271 | 1.271 | 691.4 | 691 |
| 4 | 1.172 | 1.172 | 61.23 | 61.2 |
| 5 | 1.113 | 1.113 | 119.4 | 119 |
| 6 | 1.042 | 1.042 | 40.82 | 40.8 |
| 7 | 1.033 | 1.033 | 1.343 | 1.34 |
| 8 | 1.017 | 1.017 | 7.883 | 7.88 |
| 9 | 1.009 | 1.009 | 1.343 (min-rule) | 1.34 |

Last sigma^2 (k = 9): Mack min-rule 1.343; ChainLadder log-linear rule 0.6454 (slope p-value 0.0008, so the package default does use the log-linear value). Mack (1994) p. 130 quotes the same two numbers as exp(-0.44) = 0.64 and 1.34 and chooses the min-rule as "a bit more on the safe side".

## 3. Exhibit 1: published R value, our value, difference

Ultimate, IBNR and Mack S.E. per accident year. R prints integers per year and two decimals for the totals; "diff" is ours minus R.

| AY | Ult (R) | Ult (ours) | diff | IBNR (R) | IBNR (ours) | diff | S.E. (R) | S.E. (ours) | diff |
|---|---|---|---|---|---|---|---|---|---|
| 1981 | 18,834 | 18,834.0 | 0.00 | 0 | 0.0 | 0.00 | 0 | 0.0 | 0.00 |
| 1982 | 16,858 | 16,858.0 | -0.05 | 154 | 154.0 | -0.05 | 206 | 206.2 | +0.22 |
| 1983 | 24,083 | 24,083.4 | +0.37 | 617 | 617.4 | +0.37 | 623 | 623.4 | +0.38 |
| 1984 | 28,703 | 28,703.1 | +0.14 | 1,636 | 1,636.1 | +0.14 | 747 | 747.2 | +0.18 |
| 1985 | 28,927 | 28,926.7 | -0.26 | 2,747 | 2,746.7 | -0.26 | 1,469 | 1,469.5 | +0.46 |
| 1986 | 19,501 | 19,501.1 | +0.10 | 3,649 | 3,649.1 | +0.10 | 2,002 | 2,001.9 | -0.14 |
| 1987 | 17,749 | 17,749.3 | +0.30 | 5,435 | 5,435.3 | +0.30 | 2,209 | 2,209.2 | +0.24 |
| 1988 | 24,019 | 24,019.2 | +0.19 | 10,907 | 10,907.2 | +0.19 | 5,358 | 5,357.9 | -0.13 |
| 1989 | 16,045 | 16,045.0 | -0.02 | 10,650 | 10,650.0 | -0.02 | 6,333 | 6,333.2 | +0.17 |
| 1990 | 18,402 | 18,402.4 | +0.44 | 16,339 | 16,339.4 | +0.44 | 24,566 | 24,566.3 | +0.29 |
| Total | 213,122.23 | 213,122.23 | -0.00 | 52,135.23 | 52,135.23 | -0.00 | 26,909.01 | 26,909.01 | +0.00 |

Every per-year difference is below 0.5 in absolute value, which is the rounding of R's integer print. The totals agree to the two printed decimals (actual gaps: Ultimate -0.0017, IBNR -0.0017, S.E. +0.0012, all inside half a unit of the last printed digit).

Attribution of the differences: all rounding. No formula variant and no sigma-rule difference is involved in this exhibit because the vignette call fixes `est.sigma = "Mack"`, which is the rule the formalization uses.

## 4. Diagnosis: the sigma rule and the package default

R ChainLadder's default is `est.sigma = "log-linear"`, not Mack's rule. `estimate.sigma()` fits `lm(log(sigma_k) ~ k)` over the development periods where sigma_k is estimable and positive (k = 1..8 here) and extrapolates to k = 9; `Mack.S.E()` keeps that value when the slope p-value is at most 0.05 and otherwise overwrites `est.sigma` with "Mack". On RAA the p-value is 0.0008, so the default output uses the log-linear last sigma.

Same triangle, our formulas, last sigma^2 replaced by 0.6454 (log-linear):

| AY | S.E. min-rule | S.E. log-linear | diff |
|---|---|---|---|
| 1981 | 0.0 | 0.0 | 0.00 |
| 1982 | 206.2 | 142.9 | -63.29 |
| 1983 | 623.4 | 592.1 | -31.23 |
| 1984 | 747.2 | 712.9 | -34.32 |
| 1985 | 1,469.5 | 1,452.1 | -17.37 |
| 1986 | 2,001.9 | 1,995.0 | -6.87 |
| 1987 | 2,209.2 | 2,203.8 | -5.40 |
| 1988 | 5,357.9 | 5,354.3 | -3.53 |
| 1989 | 6,333.2 | 6,331.5 | -1.62 |
| 1990 | 24,566.3 | 24,565.8 | -0.51 |
| Total | 26,909.01 | 26,880.74 | -28.27 |

The published default-rule totals (ChainLadder reference page for `summary.MackChainLadder`, call `MackChainLadder(Triangle = RAA)`) are Mack S.E. 26,880.74 and CV(IBNR) 0.5155965; ours are 26,880.74 and 0.515596. Both sigma rules therefore reproduce R; which one applies is decided by the `est.sigma` argument and nothing else. Ultimates and IBNR do not depend on the rule.

So, for anyone comparing against R: the commonly quoted total Mack S.E. of 26,909 is the `est.sigma = "Mack"` figure (and Mack's own 1994 figure); a plain `MackChainLadder(RAA)` prints 26,881. The whole 28-point gap is the last sigma. Every year's standard error moves because every projection passes through f_9; the effect is largest for 1982, whose MSEP is the f_9 term alone (206 versus 143).

## 5. Exhibit 2: Mack's estimation-error term versus the conditional-resampling term

Per accident year, with a_k = sigma_k^2 / (f_k^2 S_k) and the sum or product over the factors the year still needs:

Mack: Chat_i^2 sum_k a_k. Conditional resampling (BBMW form): Chat_i^2 (prod_k (1 + a_k) - 1).

The s.e. columns are square roots of these single-year estimation-error terms alone, not the full MSEP. "Share of MSEP" is the difference of the squared terms divided by the year's full Mack MSEP (process plus estimation). Min-rule sigma throughout.

| AY | IBNR | Mack est. s.e. | resampling est. s.e. | diff of squares | rel. diff | share of MSEP |
|---|---|---|---|---|---|---|
| 1982 | 154 | 141.7 | 141.7 | 0.0 | 0.000% | 0.000% |
| 1983 | 617 | 410.0 | 410.0 | 9.0 | 0.005% | 0.002% |
| 1984 | 1,636 | 507.2 | 507.2 | 18.1 | 0.007% | 0.003% |
| 1985 | 2,747 | 808.8 | 808.9 | 141.0 | 0.022% | 0.007% |
| 1986 | 3,649 | 825.4 | 825.6 | 364.3 | 0.053% | 0.009% |
| 1987 | 5,435 | 844.0 | 844.3 | 566.9 | 0.080% | 0.012% |
| 1988 | 10,907 | 2,056.6 | 2,058.5 | 7,657.5 | 0.181% | 0.027% |
| 1989 | 10,650 | 1,920.8 | 1,925.2 | 16,653.6 | 0.451% | 0.042% |
| 1990 | 16,339 | 7,275.9 | 7,324.8 | 714,159.9 | 1.349% | 0.118% |
| Sum of single-year terms | 52,135 | 7,959.3 | 8,005.6 | 739,570.4 | 1.167% | |
| Total incl. cross terms | 52,135 | 10,153.3 | 10,193.0 | 807,523.3 | 0.783% | 0.112% |

The "total incl. cross terms" row uses the total-reserve analogue of each term: sum over ordered pairs (i, j) of Chat_i Chat_j times sum_k a_k (Mack) or prod_k (1 + a_k) - 1 (resampling), with k running over the factors both years share. The Mack row of that total is verified in the script to add up with the process variance to Mack's total MSEP (the cross-term formula in `mack()`).

Reading. The resampling term is always at least Mack's (prod (1 + a_k) - 1 >= sum a_k for a_k >= 0) and the excess is second order in the a_k, so it only shows where the a_k are not tiny. On RAA the a_k are small for every k except k = 1, where sigma_1^2 = 27,883 is large relative to S_1 = 21,829; a_1 = 27883 / (2.999^2 x 21,829) = 0.142, against a_k of 0.007 or less for every k >= 2. That is why 1990 alone carries 714,160 of the 739,570 single-year excess (97 percent), and why the single-year excess for 1982 is exactly zero (one factor, so product and sum coincide). In total standard-error terms: Mack 26,909.01 versus 26,924.01 with the resampling estimation error, a 0.06 percent change. Process variance (621.0 million) dominates estimation error (103.1 million Mack, 103.9 million resampling) on this triangle, which is why the formula choice is nearly invisible at the total level.

## 6. Surprises and cautions

1. The R package default does not reproduce Mack (1994) or the widely quoted 26,909. It prints 26,881, because its default last-sigma rule is the log-linear regression that Mack mentions and declines. Both numbers are correct implementations of their respective rules; anyone citing "the R number" should say which.
2. The log-linear fit is not marginal on RAA (p = 0.0008), so the fallback to Mack's rule that the package documents never triggers here.
3. Mack's total MSEP cross-term formula and the pairwise form used for the resampling total agree exactly in the Mack case (assertion in the script), a small consistency check on the cross terms as written in `reproduce_mack1993.py`.
4. On RAA the Mack versus resampling gap is negligible at the total level and only visible for the youngest year. A triangle with larger a_k (small S_k or large sigma_k^2 in several periods) would separate the two formulas more; RAA is not that triangle.

## 7. Reproduce

    cd experiments/variance-mack-2027/case_study
    python3 build_raa_csv.py             # rebuild raa_cumulative.csv and re-check the three sources (needs network once)
    python3 raa_case_study.py            # prints all exhibits and LaTeX bodies, exit 0 iff R is reproduced
    python3 raa_case_study.py --json     # also writes raa_case_study_results.json
    python3 raa_case_study.py --json > run_output.txt

Requirements: Python 3 with scipy (only `scipy.stats.linregress`, for the log-linear p-value). The script imports `mack` and `load_triangle` from `../reproduce_mack1993.py`.
