# Theorem-aware reserving audit: CAS Schedule P database, cumulative paid, year-end 1997

`audit.py` writes this report (one command: `./run.sh`). Certificates per company are in `certificates/<line>_<GRCODE>.json`; machine-readable aggregates in `summary.json`; LaTeX table bodies in `tables.tex`; sources and hashes in `SOURCES.md`.

Dataset: ppauto 146, wkcomp 132, comauto 158, medmal 34, prodliab 70, othliab 239 companies (779 total). Audited 638, skipped 141 (degenerate). All audited Mack data hypotheses hold on 354; adding the BF lemma's data-side condition f_k >= 1, on 266.

## Findings

The database holds 779 company triangles (ppauto 146, wkcomp 132, comauto 158, medmal 34, prodliab 70, othliab 239). 141 are degenerate (51 all zero, 90 with fewer than three accident years carrying a nonzero latest diagonal) and were skipped; 638 were audited. On 409 of the 638 the chain ladder is defined in the sense that every column sum S_k, every factor f_k and every latest-diagonal value is nonzero; on 354 every data hypothesis of the machine-checked Mack theorems holds (nonnegative cells, S_k != 0, nonzero contributor cells in the estimable columns, f_k != 0, a_k >= 0, at least two nonzero contributors per estimable column). Adding the f_k >= 1 hypothesis of the Bornhuetter-Ferguson fraction lemma leaves 266: decreasing cumulative paid is common in the late columns (32 data-clean triangles have f_7 < 1, 27 have f_8 < 1), and 73 of the 354 data-clean triangles carry a negative reserve in at least one accident year.

The dominant hypothesis failure is S_k = 0 (161 audited triangles), and in 154 of these the 1988 accident year is empty: the company started writing during the decade, so the late development columns contain no data at all and f_k = 0 under the x/0 = 0 convention. Zero contributor cells (262 triangles) and a zero latest diagonal (228) mostly coincide with the same companies. Negative cumulative paid cells occur in 37 audited triangles (19 with a negative latest-diagonal value), which makes the process-variance term negative and, in two triangles, pushes the estimation share of MSEP above 100 percent; these are excluded from the data-clean set. Two companies (GRCODE 38997 in comauto and wkcomp) report constant rows, so every f_k = 1, every sigma_k^2 = 0 and the reserve is zero; and the wkcomp triangles of GRCODE 13994 and GRCODE 10657 are identical cell for cell.

On the data-clean set the total estimation-error term of the conditional-resampling (BBMW) estimator exceeds Mack's by a median 0.095 percent (Q1 0.022, Q3 0.387, max 10.6 percent). Relative excess is defined on 352 of the 354 data-clean triangles because the Mack estimation-error denominator is zero in the two constant-row triangles. The excess exceeds 1 percent on 36 of 352 triangles (othliab 26, comauto 6, prodliab 4, none in ppauto, wkcomp or medmal), 5 percent on 6, and 10 percent on 1 (prodliab GRCODE 1066). The excess is concentrated among smaller triangles: the median is 0.44 percent in the smallest third of triangles by paid-to-date (median 1.9 million) against 0.019 percent in the largest third (median 123 million), the 36 triangles above 1 percent hold 1.4 percent of the pooled data-clean reserve, and the pooled excess (sum of BBMW terms over sum of Mack terms) is 0.18 percent. In terms of total standard error the ratio BBMW to Mack has median 1.0001 and maximum 1.031. The largest relative estimation variance max_k a_k has median 0.40 percent overall (ppauto 0.09, wkcomp 0.13, comauto 0.46, medmal 2.4, prodliab 2.9, othliab 2.5) and sits in the first column on 259 of 354 triangles; the estimation-error share of total Mack MSEP has median 33 percent (Q1 25, Q3 46). Four audit-relevant deterministic identities were checked numerically on every audited triangle where their hypotheses hold: the 1999 recursion equals the 1993 closed form, Mack <= BBMW, the one-factor equality, and the second-order bound; the observed remainder is between 41 and 63 percent of the bound Chat^2 (exp(sum a) - 1 - sum a) on the middle half of the data-clean set.

The last-sigma rule matters more often than the estimation-error variant. The log-linear comparison is defined on 350 of 354 data-clean triangles; the other four have fewer than two positive estimable sigma_k^2 values. Replacing Mack's min-rule by the ChainLadder log-linear rule changes the total Mack standard error by more than 1 percent on 87 of those 350 triangles, by more than 5 percent on 29 and by more than 10 percent on 16, with a median change of 0.0 percent. The observed maximum is 16,926 percent on othliab GRCODE 14451 because 123 data-clean triangles have sigma_k^2 = 0 in at least one estimable column (all contributors develop identically, typically fully paid), the min-rule then returns 0 while a log-linear fit through the remaining positive values extrapolates upward. Under the package default, which falls back to the min-rule when the slope p-value exceeds 0.05, the counts are 53, 10 and 4 and the largest change is 14.4 percent. The min-rule takes the b^2/a branch on 262 data-clean triangles and the min(a, b) branch on 92. The reference implementation mack() raises a division-by-zero error on 69 data-clean triangles, all with sigma_6^2 = 0, which is exactly the case the Lean convention x/0 = 0 handles; the audit script mirrors mack() bit for bit wherever mack() is defined and this is asserted at run time.

## Aggregate tables

### Table 1. Triangles, audits, hypothesis status, and threshold counts

Excess = (BBMW - Mack)/Mack of the total estimation-error term (cross terms included). LL = |relative change in total Mack S.E.| when the last sigma is extrapolated log-linearly instead of by the min-rule. Counts on the data-clean set.

| Line | Companies | Audited | Skipped | CL defined | All Mack data hyps | + BF f>=1 | Excess >1% | >5% | >10% | LL >1% | >5% | >10% | LL default >1% | >5% | >10% |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 146 | 128 | 18 | 95 | 88 | 61 | 0 | 0 | 0 | 13 | 2 | 0 | 11 | 1 | 0 |
| Workers' compensation | 132 | 104 | 28 | 59 | 58 | 51 | 0 | 0 | 0 | 25 | 6 | 2 | 20 | 5 | 1 |
| Commercial auto/truck liability/medical | 158 | 140 | 18 | 92 | 84 | 62 | 6 | 0 | 0 | 14 | 6 | 5 | 8 | 2 | 1 |
| Medical malpractice (claims made) | 34 | 25 | 9 | 14 | 12 | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Product liability (occurrence) | 70 | 45 | 25 | 22 | 14 | 12 | 4 | 1 | 1 | 3 | 1 | 1 | 2 | 0 | 0 |
| Other liability (occurrence) | 239 | 196 | 43 | 127 | 98 | 73 | 26 | 5 | 0 | 32 | 14 | 8 | 12 | 2 | 2 |
| All lines | 779 | 638 | 141 | 409 | 354 | 266 | 36 | 6 | 1 | 87 | 29 | 16 | 53 | 10 | 4 |

### Table 2. Relative excess (BBMW - Mack)/Mack of the total estimation-error term, percent

Data-clean triangles.

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 88 | 0.000 | 0.008 | 0.015 | 0.056 | 0.039 | 0.727 |
| Workers' compensation | 57 | 0.002 | 0.013 | 0.026 | 0.047 | 0.049 | 0.389 |
| Commercial auto/truck liability/medical | 83 | 0.003 | 0.056 | 0.116 | 0.286 | 0.288 | 2.720 |
| Medical malpractice (claims made) | 12 | 0.055 | 0.203 | 0.339 | 0.360 | 0.457 | 0.826 |
| Product liability (occurrence) | 14 | 0.052 | 0.486 | 0.792 | 1.807 | 1.721 | 10.635 |
| Other liability (occurrence) | 98 | -0.000 | 0.171 | 0.409 | 1.048 | 1.074 | 9.201 |
| All lines | 352 | -0.000 | 0.022 | 0.095 | 0.465 | 0.387 | 10.635 |

Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 95 | -0.018 | 0.008 | 0.015 | 0.057 | 0.045 | 0.727 |
| Workers' compensation | 58 | -1.176 | 0.013 | 0.026 | 0.026 | 0.047 | 0.389 |
| Commercial auto/truck liability/medical | 91 | 0.003 | 0.067 | 0.120 | 0.629 | 0.388 | 12.336 |
| Medical malpractice (claims made) | 14 | 0.055 | 0.217 | 0.368 | 0.403 | 0.518 | 0.826 |
| Product liability (occurrence) | 22 | 0.052 | 0.580 | 0.936 | 2.940 | 3.233 | 13.750 |
| Other liability (occurrence) | 122 | -0.000 | 0.176 | 0.510 | 1.541 | 1.443 | 22.331 |
| All lines | 402 | -1.176 | 0.025 | 0.119 | 0.802 | 0.525 | 22.331 |

### Table 3. Largest relative estimation variance max_k a_k, percent

Data-clean triangles.

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 88 | 0.000 | 0.034 | 0.093 | 0.279 | 0.220 | 3.762 |
| Workers' compensation | 58 | 0.000 | 0.073 | 0.134 | 0.264 | 0.290 | 2.877 |
| Commercial auto/truck liability/medical | 84 | 0.000 | 0.190 | 0.459 | 1.483 | 1.614 | 19.955 |
| Medical malpractice (claims made) | 12 | 0.341 | 1.200 | 2.393 | 8.431 | 4.514 | 67.645 |
| Product liability (occurrence) | 14 | 0.074 | 2.160 | 2.948 | 6.797 | 7.161 | 27.900 |
| Other liability (occurrence) | 98 | 0.000 | 0.686 | 2.525 | 6.011 | 6.790 | 45.372 |
| All lines | 354 | 0.000 | 0.106 | 0.402 | 2.683 | 2.000 | 67.645 |

Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 95 | 0.000 | 0.039 | 0.097 | 0.295 | 0.277 | 3.762 |
| Workers' compensation | 59 | 0.000 | 0.074 | 0.138 | 0.331 | 0.301 | 4.207 |
| Commercial auto/truck liability/medical | 92 | 0.000 | 0.211 | 0.517 | 4.377 | 1.793 | 127.441 |
| Medical malpractice (claims made) | 14 | 0.341 | 1.380 | 2.499 | 8.592 | 5.527 | 67.645 |
| Product liability (occurrence) | 22 | 0.074 | 2.160 | 4.691 | 21.983 | 8.573 | 316.036 |
| Other liability (occurrence) | 127 | 0.000 | 0.914 | 3.514 | 8.467 | 8.287 | 95.076 |
| All lines | 409 | 0.000 | 0.129 | 0.562 | 5.207 | 3.037 | 316.036 |

### Table 4. Estimation-error share of total Mack MSEP, percent

Data-clean triangles.

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 88 | 2.4 | 24.6 | 31.0 | 31.8 | 37.7 | 64.7 |
| Workers' compensation | 57 | 3.2 | 22.5 | 36.0 | 37.9 | 52.8 | 86.3 |
| Commercial auto/truck liability/medical | 83 | 7.2 | 29.0 | 36.5 | 37.1 | 46.0 | 88.3 |
| Medical malpractice (claims made) | 12 | 11.8 | 28.5 | 34.9 | 35.0 | 42.8 | 57.8 |
| Product liability (occurrence) | 14 | 15.6 | 30.6 | 36.4 | 38.1 | 48.0 | 58.3 |
| Other liability (occurrence) | 98 | 5.8 | 24.4 | 35.2 | 35.7 | 47.1 | 86.9 |
| All lines | 352 | 2.4 | 25.3 | 33.3 | 35.5 | 45.5 | 88.3 |

Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 95 | 2.4 | 24.9 | 31.2 | 33.0 | 38.6 | 78.1 |
| Workers' compensation | 58 | 3.2 | 21.3 | 35.0 | 37.5 | 52.0 | 86.3 |
| Commercial auto/truck liability/medical | 91 | 7.2 | 27.7 | 34.9 | 36.6 | 46.0 | 88.3 |
| Medical malpractice (claims made) | 14 | 11.8 | 29.5 | 34.9 | 35.9 | 43.3 | 57.8 |
| Product liability (occurrence) | 22 | 15.6 | 32.2 | 39.3 | 44.4 | 57.0 | 77.0 |
| Other liability (occurrence) | 122 | 5.8 | 23.2 | 35.5 | 37.0 | 48.5 | 93.6 |
| All lines | 402 | 2.4 | 25.1 | 33.6 | 36.4 | 46.8 | 93.6 |

### Table 5. Relative change in total Mack S.E., log-linear last sigma versus min-rule, percent (signed)

Data-clean triangles.

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 87 | -5.7 | 0.0 | 0.1 | 0.3 | 0.3 | 6.0 |
| Workers' compensation | 57 | -15.4 | -0.8 | 0.0 | -0.5 | 0.5 | 6.9 |
| Commercial auto/truck liability/medical | 83 | -17.1 | 0.0 | 0.0 | 1.5 | 0.2 | 55.1 |
| Medical malpractice (claims made) | 12 | -1.0 | -0.0 | 0.0 | -0.1 | 0.1 | 0.4 |
| Product liability (occurrence) | 14 | -4.3 | -0.1 | 0.0 | 41.2 | 0.3 | 581.4 |
| Other liability (occurrence) | 97 | -21.9 | 0.0 | 0.2 | 177.5 | 0.9 | 16925.9 |
| All lines | 350 | -21.9 | -0.0 | 0.0 | 51.2 | 0.5 | 16925.9 |

Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 94 | -18.2 | 0.0 | 0.0 | 0.1 | 0.3 | 6.0 |
| Workers' compensation | 58 | -15.4 | -0.7 | 0.0 | -0.5 | 0.5 | 6.9 |
| Commercial auto/truck liability/medical | 91 | -100.0 | 0.0 | 0.0 | 0.5 | 0.2 | 55.1 |
| Medical malpractice (claims made) | 14 | -1.0 | -0.1 | 0.0 | -0.1 | 0.0 | 0.4 |
| Product liability (occurrence) | 22 | -4.3 | 0.0 | 0.1 | 26.8 | 0.4 | 581.4 |
| Other liability (occurrence) | 121 | -21.9 | 0.0 | 0.2 | 142.9 | 0.9 | 16925.9 |
| All lines | 400 | -100.0 | 0.0 | 0.0 | 44.8 | 0.5 | 16925.9 |

### Table 6. Same as Table 5 under the ChainLadder default (log-linear only if slope p <= 0.05, else min-rule), percent

Data-clean triangles.

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 87 | -5.7 | 0.0 | 0.0 | 0.2 | 0.3 | 3.3 |
| Workers' compensation | 57 | -15.4 | -0.2 | 0.0 | -0.4 | 0.3 | 6.9 |
| Commercial auto/truck liability/medical | 83 | -4.7 | 0.0 | 0.0 | 0.2 | 0.1 | 14.4 |
| Medical malpractice (claims made) | 12 | -1.0 | -0.0 | 0.0 | -0.1 | 0.0 | 0.2 |
| Product liability (occurrence) | 14 | -4.3 | -0.1 | 0.0 | -0.4 | 0.0 | 0.4 |
| Other liability (occurrence) | 97 | -11.2 | 0.0 | 0.0 | -0.2 | 0.1 | 2.9 |
| All lines | 350 | -15.4 | 0.0 | 0.0 | -0.0 | 0.2 | 14.4 |

Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 94 | -18.2 | 0.0 | 0.0 | 0.0 | 0.3 | 3.3 |
| Workers' compensation | 58 | -15.4 | -0.2 | 0.0 | -0.4 | 0.3 | 6.9 |
| Commercial auto/truck liability/medical | 91 | -4.7 | 0.0 | 0.0 | 0.5 | 0.1 | 22.4 |
| Medical malpractice (claims made) | 14 | -1.0 | -0.1 | 0.0 | -0.1 | 0.0 | 0.2 |
| Product liability (occurrence) | 22 | -4.3 | 0.0 | 0.0 | 0.1 | 0.0 | 7.7 |
| Other liability (occurrence) | 121 | -11.2 | 0.0 | 0.0 | 0.3 | 0.2 | 36.4 |
| All lines | 400 | -18.2 | 0.0 | 0.0 | 0.1 | 0.2 | 36.4 |

### Table 7. Largest single-accident-year relative excess (BBMW - Mack)/Mack, percent

Data-clean triangles.

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 88 | 0.00 | 0.02 | 0.04 | 0.13 | 0.12 | 2.91 |
| Workers' compensation | 57 | 0.00 | 0.04 | 0.07 | 0.12 | 0.14 | 1.04 |
| Commercial auto/truck liability/medical | 83 | 0.01 | 0.14 | 0.29 | 0.68 | 0.64 | 5.76 |
| Medical malpractice (claims made) | 12 | 0.12 | 0.60 | 0.94 | 1.16 | 1.61 | 2.66 |
| Product liability (occurrence) | 14 | 0.12 | 1.47 | 2.10 | 4.95 | 5.39 | 25.09 |
| Other liability (occurrence) | 98 | -0.00 | 0.54 | 1.13 | 2.90 | 3.42 | 28.55 |
| All lines | 352 | -0.00 | 0.06 | 0.22 | 1.26 | 1.01 | 28.55 |

Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:

| Line | N | min | Q1 | median | mean | Q3 | max |
|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 95 | 0.00 | 0.02 | 0.04 | 0.13 | 0.12 | 2.91 |
| Workers' compensation | 58 | 0.00 | 0.04 | 0.07 | 0.12 | 0.14 | 1.04 |
| Commercial auto/truck liability/medical | 91 | 0.01 | 0.15 | 0.32 | 1.89 | 0.81 | 62.22 |
| Medical malpractice (claims made) | 14 | 0.12 | 0.66 | 1.10 | 1.22 | 1.63 | 2.66 |
| Product liability (occurrence) | 22 | 0.12 | 1.47 | 3.20 | 6.27 | 8.44 | 25.09 |
| Other liability (occurrence) | 127 | -0.00 | 0.54 | 1.21 | 3.67 | 4.36 | 46.85 |
| All lines | 407 | -0.00 | 0.06 | 0.30 | 2.00 | 1.40 | 62.22 |

### Table 8. Hypothesis failures among audited triangles (a triangle can fail several)

| Line | Audited | cells_nonneg | S_nonzero | C_contributors_nonzero | latest_diagonal_nonzero | f_nonzero | relvar_nonneg | sigma_df | f_ge_one |
|---|---|---|---|---|---|---|---|---|---|
| Private passenger auto liability/medical | 128 | 3 | 28 | 38 | 33 | 28 | 1 | 28 | 58 |
| Workers' compensation | 104 | 3 | 31 | 44 | 45 | 31 | 2 | 30 | 41 |
| Commercial auto/truck liability/medical | 140 | 6 | 39 | 51 | 48 | 39 | 2 | 39 | 65 |
| Medical malpractice (claims made) | 25 | 1 | 11 | 12 | 11 | 11 | 1 | 11 | 16 |
| Product liability (occurrence) | 45 | 8 | 13 | 29 | 22 | 14 | 6 | 15 | 25 |
| Other liability (occurrence) | 196 | 16 | 39 | 88 | 69 | 40 | 6 | 44 | 85 |
| All lines | 638 | 37 | 161 | 262 | 228 | 163 | 18 | 167 | 290 |

### Table 9. Skip reasons

| Line | Skipped | Reason: all zero | Reason: fewer than 3 nonzero latest-diagonal years |
|---|---|---|---|
| Private passenger auto liability/medical | 18 | 1 | 17 |
| Workers' compensation | 28 | 6 | 22 |
| Commercial auto/truck liability/medical | 18 | 4 | 14 |
| Medical malpractice (claims made) | 9 | 4 | 5 |
| Product liability (occurrence) | 25 | 13 | 12 |
| Other liability (occurrence) | 43 | 23 | 20 |
| All lines | 141 | 51 | 90 |

### Table 10. Ten data-clean triangles with the largest total relative excess

| Line | GRCODE | Company | Reserve | Excess % | max a_k % | argmax k | Total S.E. ratio (BBMW/Mack) |
|---|---|---|---|---|---|---|---|
| prodliab | 1066 | Island Ins Cos Grp | 7,452 | 10.64 | 24.52 | 3 | 1.0305 |
| othliab | 13641 | Colorado Farm Bureau Mut Ins Co | 799 | 9.20 | 27.28 | 5 | 1.0275 |
| othliab | 13439 | Partners Mut Ins Co | 154 | 8.38 | 45.37 | 1 | 1.0204 |
| othliab | 2208 | Oklahoma Farm Grp | 576 | 6.95 | 36.56 | 1 | 1.0163 |
| othliab | 9466 | Lumber Ins Cos | 563 | 6.05 | 18.10 | 1 | 1.0018 |
| othliab | 13994 | Fremont Mut Ins Co | 371 | 5.16 | 21.01 | 0 | 1.0049 |
| othliab | 1066 | Island Ins Cos Grp | -485 | 3.98 | 7.44 | 8 | 1.0172 |
| prodliab | 2143 | Farmers Alliance Mut & Affiliates | 263 | 3.86 | 8.77 | 2 | 1.0058 |
| othliab | 15199 | Standard Mut Ins Co | 199 | 3.82 | 7.60 | 1 | 1.0069 |
| othliab | 13943 | Fitchburg Mut Ins Co | 250 | 3.36 | 12.57 | 0 | 1.0041 |

## Duplicate triangles within a line (identical 55 upper cells, not all zero)

- wkcomp: GRCODE 13994 (Fremont Mut Ins Co) equals GRCODE 10657 (First Mercury Ins Co)
