# Reference computations

The Lean definitions are stated over the reals and are not executable. These Python 3.10 or later scripts implement the same definitions with the same index conventions, so that quoted numerical results can be regenerated and compared with the literature. `reproduce_mack1993.py` uses only the standard library. The RAA case study requires SciPy, and the Schedule P audit requires NumPy, Pandas, and SciPy; exact tested versions are pinned in `requirements.txt`. These are reference computations, not the Lean code, and agreement between the two is checked numerically rather than proved.

From the repository root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r scripts/requirements.txt
python3 scripts/reproduce_mack1993.py
python3 scripts/case_study/raa_case_study.py
python3 scripts/audit/audit.py --selftest
```

- `reproduce_mack1993.py`: Mack (1993), Section 4, on the Taylor and Ashe (1983) triangle in `data/`. Reproduces every printed value of Mack's Tables 2 and 3 (reserves, standard errors, the total 18,681 at 13 percent). `--catalogue` prints Mack's estimation-error term beside the conditional-resampling term of Buchwalder, Bühlmann, Merz and Wüthrich (2006) for each accident year.
- `case_study/raa_case_study.py`: the RAA triangle against the published output of R's `ChainLadder` (`MackChainLadder(RAA, est.sigma = "Mack")`), which it matches to printed precision; with the package's default log-linear rule for the last variance parameter it reproduces the other commonly quoted total (26,881 against 26,909). Details in `case_study/CASE_STUDY.md`.
- `audit/`: the theorem-aware audit of the CAS Schedule P database (Meyers and Shi 2011): `./run.sh` downloads the six public CSV files (hashes in `SOURCES.md`), then `audit.py` writes one certificate per company triangle recording which data hypotheses of the machine-checked theorems hold, where an approximation or a convention enters, the Mack and conditional-resampling estimation-error terms, the sensitivity to the last-period variance rule, and numerical checks of every deterministic theorem instance. Aggregates in `summary.json` and `AUDIT_RESULTS.md`.

Conventions shared with the Lean development: accident years and development years are zero-based; a column with no dispersion has variance parameter zero (the Lean field convention `x / 0 = 0` makes the corresponding terms vanish); Mack's minimum rule for the last variance parameter is a convention used by no theorem, and the audit reports the log-linear alternative beside it.
