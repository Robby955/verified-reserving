#!/usr/bin/env python3
"""Theorem-aware reserving audit over the CAS Schedule P loss reserving database.

For every company triangle in the six lines (cumulative paid, upper triangle as
of year-end 1997) this script evaluates the formalized Mack chain-ladder
definitions (VerifiedReserving/ChainLadder.lean, Msep.lean, Catalogue.lean) and
records, in a certificate JSON, which audited data-side hypotheses hold on that
triangle and where the approximations enter. Distributional assumptions that
cannot be checked from one observed triangle are not certified by the audit.

Numerics follow ../reproduce_mack1993.py `mack()` exactly (zero-based indices,
f_k from contributing rows, sigma_k^2 with divisor n-k-2, Mack's min-rule for
the last sigma^2, per-year MSEP with process and estimation terms, total MSEP
with cross terms) with one extension: division by zero returns 0, which is the
convention of the Lean definitions (x / 0 = 0 in Mathlib). On every triangle
where `mack()` runs without a ZeroDivisionError the two agree bit for bit; this
is asserted at run time.

Usage: python3 audit.py            (reads data/*.csv, writes certificates/, summary.json,
                                    aggregate_tables.md, tables.tex, AUDIT_RESULTS.md)
       python3 audit.py --selftest (only the reproduction checks on Taylor-Ashe and RAA)
"""
import csv
import glob
import hashlib
import json
import math
import os
import sys
from collections import Counter, defaultdict

import numpy as np
import pandas as pd
from scipy.stats import linregress

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)
sys.path.insert(0, PARENT)
sys.path.insert(0, os.path.join(PARENT, "case_study"))
from reproduce_mack1993 import load_triangle, mack  # noqa: E402
from raa_case_study import last_sigma_loglinear, msep_with_sigma, estimation_error_terms  # noqa: E402

LINES = [
    ("ppauto", "Private passenger auto liability/medical"),
    ("wkcomp", "Workers' compensation"),
    ("comauto", "Commercial auto/truck liability/medical"),
    ("medmal", "Medical malpractice (claims made)"),
    ("prodliab", "Product liability (occurrence)"),
    ("othliab", "Other liability (occurrence)"),
]
LINE_LABEL = dict(LINES)
N = 10
LAST_CALENDAR_YEAR = 1997
FIRST_ACCIDENT_YEAR = 1988


def sdiv(a, b):
    """Division with the Lean/Mathlib convention x / 0 = 0."""
    return a / b if b != 0 else 0.0


# ----------------------------------------------------------------------------
# Total-function mirror of mack() (same expression order, safe division)
# ----------------------------------------------------------------------------

def basics_total(C):
    """f_k, S_k, T_k and the estimable sigma_k^2 (k <= n-3, else None); Lean convention."""
    n = len(C)
    f, S, T, sig2 = [], [], [], []
    for k in range(n - 1):
        idx = range(n - k - 1)
        Sk = sum(C[i][k] for i in idx)
        Tk = sum(C[i][k + 1] for i in idx)
        f.append(sdiv(Tk, Sk))
        S.append(Sk)
        T.append(Tk)
    for k in range(n - 1):
        m = n - k - 2
        if m >= 1:
            sig2.append(sdiv(sum(C[i][k] * (sdiv(C[i][k + 1], C[i][k]) - f[k]) ** 2 for i in range(n - k - 1)), m))
        else:
            sig2.append(None)
    return f, S, T, sig2


def last_sigma_mack_total(sig2):
    n = len(sig2) + 1
    a, b = sig2[n - 4], sig2[n - 3]
    return min(sdiv(b * b, a), min(a, b))


def project_total(C, f):
    n = len(C)
    Chat = [[None] * n for _ in range(n)]
    for i in range(n):
        d = n - 1 - i
        Chat[i][d] = C[i][d]
        for k in range(d, n - 1):
            Chat[i][k + 1] = Chat[i][k] * f[k]
    return Chat


def msep_total(C, f, S, sig2):
    """Per-year MSEP and total MSEP (with cross terms), same formulas as mack()."""
    n = len(C)
    Chat = project_total(C, f)
    ult = [Chat[i][n - 1] for i in range(n)]
    msep = []
    for i in range(n):
        d = n - 1 - i
        s = sum(sdiv(sig2[k], f[k] ** 2) * (sdiv(1.0, Chat[i][k]) + sdiv(1.0, S[k])) for k in range(d, n - 1))
        msep.append(ult[i] ** 2 * s)
    total = sum(msep)
    for i in range(n):
        d = n - 1 - i
        later = sum(ult[j] for j in range(i + 1, n))
        total += ult[i] * later * sum(sdiv(sdiv(2 * sig2[k], f[k] ** 2), S[k]) for k in range(d, n - 1))
    return Chat, ult, msep, total


def relvar_total(f, S, sig2):
    """a_k = sigma_k^2 / f_k^2 / S_k (Catalogue.relVar), same order as the case study."""
    return [sdiv(sdiv(sig2[k], f[k] ** 2), S[k]) for k in range(len(f))]


def estimation_terms_total(ult, a_k):
    """Per year: Mack term, BBMW term, second-order bound Chat^2 (exp(sum a) - 1 - sum a)."""
    n = len(ult)
    out = []
    for i in range(n):
        d = n - 1 - i
        a = a_k[d:]
        s = sum(a)
        p = 1.0
        for x in a:
            p *= 1 + x
        u2 = ult[i] ** 2
        out.append(dict(mack=u2 * s, bbmw=u2 * (p - 1), bound=u2 * (math.exp(s) - 1 - s), sum_a=s, n_factors=len(a)))
    return out


def total_terms(C, f, S, sig2, Chat, ult, a_k):
    """Total-reserve decomposition: process, Mack estimation, BBMW estimation, bound (all with cross terms)."""
    n = len(C)
    est_mack = est_bbmw = bound = 0.0
    for i in range(1, n):
        for j in range(1, n):
            d = max(n - 1 - i, n - 1 - j)
            common = a_k[d:]
            s = sum(common)
            p = 1.0
            for x in common:
                p *= 1 + x
            est_mack += ult[i] * ult[j] * s
            est_bbmw += ult[i] * ult[j] * (p - 1)
            bound += ult[i] * ult[j] * (math.exp(s) - 1 - s)
    proc = sum(ult[i] ** 2 * sum(sdiv(sdiv(sig2[k], f[k] ** 2), Chat[i][k]) for k in range(n - 1 - i, n - 1)) for i in range(1, n))
    return proc, est_mack, est_bbmw, bound


def se2rec_total(C, f, S, sig2, Chat, i, m):
    """m steps of Mack's 1999 recursion (Recursion.lean `se2rec`), Lean convention."""
    n = len(C)
    v = 0.0
    for step in range(m):
        k = n - 1 - i + step
        v = Chat[i][k] ** 2 * (sdiv(sig2[k], Chat[i][k]) + sdiv(sig2[k], S[k])) + v * f[k] ** 2
    return v


def loglinear_last_sigma(sig2_est):
    """ChainLadder estimate.sigma() log-linear rule, reused from the RAA case study.
    Returns (sigma_last^2, p-value) or (None, None) when fewer than 2 positive sigma_k."""
    n = len(sig2_est) + 1
    pos = [k for k in range(n - 1) if sig2_est[k] is not None and sig2_est[k] > 0]
    if len(pos) < 2:
        return None, None
    if len(pos) == 2:
        # linregress p-value is undefined with two points (zero residual df); fit by hand
        ks = [k + 1 for k in pos]
        ys = [math.log(math.sqrt(sig2_est[k])) for k in pos]
        slope = (ys[1] - ys[0]) / (ks[1] - ks[0])
        pred = math.exp(ys[0] + slope * ((n - 1) - ks[0]))
        return pred * pred, None
    return last_sigma_loglinear(sig2_est)


# ----------------------------------------------------------------------------
# Certificate for one triangle
# ----------------------------------------------------------------------------

def quantiles(xs):
    xs = [float(x) for x in xs if x is not None and math.isfinite(x)]
    if not xs:
        return dict(n=0)
    a = np.array(xs)
    return dict(n=int(a.size), min=float(a.min()), q1=float(np.percentile(a, 25)), median=float(np.median(a)),
                mean=float(a.mean()), q3=float(np.percentile(a, 75)), max=float(a.max()))


def audit_triangle(C, meta):
    n = len(C)
    cert = dict(meta)
    cert["n"] = n
    latest = [C[i][n - 1 - i] for i in range(n)]
    upper_cells = [(i, k, C[i][k]) for i in range(n) for k in range(n - i)]
    n_zero = sum(1 for _, _, v in upper_cells if v == 0)
    n_neg = sum(1 for _, _, v in upper_cells if v < 0)
    rows_with_data = sum(1 for i in range(n) if any(C[i][k] != 0 for k in range(n - i)))
    n_latest_nonzero = sum(1 for v in latest if v != 0)
    zero_then_nonzero = sum(1 for i in range(n) for k in range(n - 1 - i) if C[i][k] == 0 and C[i][k + 1] != 0)
    cert["structural"] = dict(
        n=n,
        accident_years_with_nonzero_latest_diagonal=n_latest_nonzero,
        accident_years_with_any_nonzero_cell=rows_with_data,
        zero_cells=n_zero, negative_cells=n_neg,
        zero_cell_followed_by_nonzero=zero_then_nonzero,
        latest_diagonal=latest,
    )
    all_zero = all(v == 0 for _, _, v in upper_cells)
    if all_zero or n_latest_nonzero < 3:
        cert["status"] = "skipped"
        cert["skip_reason"] = ("all upper-triangle cells are zero" if all_zero
                               else f"only {n_latest_nonzero} accident years with a nonzero latest-diagonal value (need 3)")
        return cert
    cert["status"] = "audited"

    # --- deterministic layer (Lean convention) ---
    f, S, T, sig2_est = basics_total(C)
    sig2 = list(sig2_est)
    sig2[n - 2] = last_sigma_mack_total(sig2_est)
    Chat, ult, msep, total = msep_total(C, f, S, sig2)
    res = [ult[i] - latest[i] for i in range(n)]
    a_k = relvar_total(f, S, sig2)
    per_year = estimation_terms_total(ult, a_k)
    proc_tot, est_mack_tot, est_bbmw_tot, bound_tot = total_terms(C, f, S, sig2, Chat, ult, a_k)

    # --- cross-check against the reference implementation where it is defined ---
    ref = None
    try:
        ref = mack(C)
    except ZeroDivisionError:
        pass
    cert["reference_mack_defined"] = ref is not None
    if ref is not None:
        rf, rsig2, rres, rmsep, rtotal = ref
        assert rf == f and rsig2 == sig2 and rres == res and rmsep == msep and rtotal == total, meta
        _u, _m, _t = msep_with_sigma(C, f, S, sig2)
        assert _m == msep and _t == total
        _terms = estimation_error_terms(C, f, S, sig2)
        assert all(_terms[i][0] == per_year[i]["mack"] and _terms[i][1] == per_year[i]["bbmw"] for i in range(n))
    # decomposition identity (exact in arithmetic; floating tolerance here)
    assert abs(proc_tot + est_mack_tot - total) <= 1e-9 * max(1.0, abs(total)), meta

    # --- column-level hypothesis checks ---
    contributors = [n - k - 1 for k in range(n - 1)]
    eff_contributors = [sum(1 for i in range(n - k - 1) if C[i][k] != 0) for k in range(n - 1)]
    zero_S = [k for k in range(n - 1) if S[k] == 0]                       # theorem hypothesis S_k != 0, k+2 <= n
    zero_contrib_cells = [[i, k] for k in range(n - 2) for i in range(n - k - 1) if C[i][k] == 0]  # sigma^2 unbiasedness needs C_ik != 0, k+3 <= n
    zero_diag_rows = [i for i in range(n) if latest[i] == 0]             # 1/Chat_{i,d} in msep
    f_nonpos = [k for k in range(n - 1) if f[k] <= 0]
    f_below_one = [k for k in range(n - 1) if f[k] < 1]
    a_neg = [k for k in range(n - 1) if a_k[k] < 0]
    few_contrib = [k for k in range(n - 2) if eff_contributors[k] < 2]   # estimable column with < 2 nonzero contributors
    sig2_zero_est = [k for k in range(n - 2) if sig2_est[k] == 0]

    # --- last sigma: min-rule versus log-linear ---
    ll2, pval = loglinear_last_sigma(sig2_est)
    ll = None
    if ll2 is not None:
        sig2_ll = list(sig2_est)
        sig2_ll[n - 2] = ll2
        _, _, msep_ll, total_ll = msep_total(C, f, S, sig2_ll)
        se_mack = math.sqrt(total) if total > 0 else 0.0
        se_ll = math.sqrt(total_ll) if total_ll > 0 else 0.0
        package_default = "log-linear" if (pval is not None and pval <= 0.05) else "Mack min-rule"
        ll = dict(sigma2_last_loglinear=ll2, slope_pvalue=pval, chainladder_default_uses=package_default,
                  total_se_min_rule=se_mack, total_se_loglinear=se_ll,
                  rel_change_total_se=(se_ll / se_mack - 1) if se_mack > 0 else None,
                  rel_change_total_se_package_default=((se_ll / se_mack - 1) if (se_mack > 0 and package_default == "log-linear") else 0.0) if se_mack > 0 else None)
    cert["last_sigma"] = dict(
        extrapolated_column=n - 2, last_estimable_column=n - 3,
        sigma2_n_minus_4=sig2_est[n - 4], sigma2_n_minus_3=sig2_est[n - 3],
        sigma2_last_min_rule=sig2[n - 2],
        min_rule_branch=("b^2/a" if sdiv(sig2_est[n - 3] ** 2, sig2_est[n - 4]) <= min(sig2_est[n - 4], sig2_est[n - 3]) else "min(a,b)"),
        loglinear=ll,
    )

    # --- estimation-error terms ---
    years = []
    for i in range(n):
        t = per_year[i]
        years.append(dict(
            accident_year=FIRST_ACCIDENT_YEAR + i, latest=latest[i], ultimate=ult[i], reserve=res[i], msep=msep[i],
            n_factors=t["n_factors"], sum_a=t["sum_a"], mack_term=t["mack"], bbmw_term=t["bbmw"],
            difference=t["bbmw"] - t["mack"],
            relative_excess=(t["bbmw"] - t["mack"]) / t["mack"] if t["mack"] > 0 else None,
            second_order_bound=t["bound"],
            bound_minus_remainder=t["bound"] - (t["bbmw"] - t["mack"]),
        ))
    tot_res = sum(res)
    cert["development_factors"] = dict(f=f, S=S, T=T, contributors=contributors, effective_nonzero_contributors=eff_contributors,
                                       all_f_ge_1=len(f_below_one) == 0, f_below_one_columns=f_below_one, f_nonpositive_columns=f_nonpos)
    cert["sigma2"] = dict(estimable=sig2_est[: n - 2], full_with_min_rule=sig2, zero_estimable_columns=sig2_zero_est,
                          divisor_n_minus_k_minus_2=[n - k - 2 for k in range(n - 2)])
    cert["relvar"] = dict(a=a_k, max_a=max(a_k), argmax_a=int(max(range(n - 1), key=lambda k: a_k[k])),
                          sum_a_youngest_row=sum(a_k), negative_columns=a_neg)
    cert["per_accident_year"] = years
    cert["total"] = dict(
        reserve=tot_res, msep_mack=total, se_mack=math.sqrt(total) if total > 0 else 0.0,
        process=proc_tot, estimation_mack=est_mack_tot, estimation_bbmw=est_bbmw_tot,
        difference=est_bbmw_tot - est_mack_tot,
        relative_excess=(est_bbmw_tot - est_mack_tot) / est_mack_tot if est_mack_tot > 0 else None,
        second_order_bound=bound_tot, bound_minus_remainder=bound_tot - (est_bbmw_tot - est_mack_tot),
        estimation_share_of_msep=est_mack_tot / total if total > 0 else None,
        se_with_bbmw=math.sqrt(proc_tot + est_bbmw_tot) if proc_tot + est_bbmw_tot > 0 else 0.0,
        se_ratio_bbmw_over_mack=(math.sqrt(proc_tot + est_bbmw_tot) / math.sqrt(total)) if total > 0 else None,
    )

    # --- hypotheses of the machine-checked theorems on this triangle ---
    neg_cells = [[i, k] for i, k, v in upper_cells if v < 0]
    hyp = dict(
        cells_nonneg=dict(statement="C_ik >= 0 for every observed cell ((M3) Var = sigma_k^2 C_ik must be nonnegative; process term uses 1/Chat_ik)",
                          holds=len(neg_cells) == 0, failing_cells=neg_cells[:20], n_failing_cells=len(neg_cells),
                          theorems=["condVar_C_eq_procVar (population form requires a nonnegative variance)", "condMsep_eq"]),
        S_nonzero=dict(statement="S_k != 0 for all k with k+2 <= n", holds=len(zero_S) == 0, failing_columns=zero_S,
                       theorems=["fhat_eq_weighted_average", "condExp_fhatRv (Theorem 2)", "condExp_ultimate_eq (Theorem 1)", "condExp_sigma2Rv"]),
        C_contributors_nonzero=dict(statement="C_ik != 0 for every contributor i of column k, k+3 <= n", holds=len(zero_contrib_cells) == 0,
                                    failing_cells=zero_contrib_cells[:20], n_failing_cells=len(zero_contrib_cells),
                                    theorems=["condExp_sigma2Rv (sigma^2 unbiasedness)"]),
        latest_diagonal_nonzero=dict(statement="C_{i,n-1-i} != 0 (the 1/Chat_{i,k} terms of msep)", holds=len(zero_diag_rows) == 0, failing_rows=zero_diag_rows,
                                     theorems=["msep definition well-posed (no x/0 = 0 in the process term)"]),
        f_nonzero=dict(statement="fhat_k != 0 for all k <= n-2", holds=len(f_nonpos) == 0 and all(f[k] != 0 for k in range(n - 1)),
                       failing_columns=[k for k in range(n - 1) if f[k] == 0], theorems=["se2rec_eq_msep (Mack 1999 = Mack 1993)"]),
        relvar_nonneg=dict(statement="a_k = sigma_k^2/(f_k^2 S_k) >= 0 for all k", holds=len(a_neg) == 0, failing_columns=a_neg,
                           theorems=["mackEstimation_le_bbmwEstimation", "bbmwEstimation_sub_mackEstimation_le"]),
        f_ge_one=dict(statement="fhat_k >= 1 for all k (BF fraction lemma)", holds=len(f_below_one) == 0, failing_columns=f_below_one,
                      theorems=["one_le_cdf", "bfReserve_nonneg", "bfReserve_le"]),
        sigma_df=dict(statement="k+3 <= n (at least two contributing rows) for sigma^2 unbiasedness; column n-2 is extrapolated",
                      estimable_columns=list(range(n - 2)), single_divisor_column=n - 3, extrapolated_column=n - 2,
                      estimable_columns_with_fewer_than_2_nonzero_contributors=few_contrib, holds=len(few_contrib) == 0),
    )
    mack_keys = ["cells_nonneg", "S_nonzero", "C_contributors_nonzero", "latest_diagonal_nonzero", "f_nonzero", "relvar_nonneg", "sigma_df"]
    hyp["all_mack_data_hypotheses_hold"] = all(hyp[k]["holds"] for k in mack_keys)
    hyp["all_data_hypotheses_including_bf_hold"] = hyp["all_mack_data_hypotheses_hold"] and hyp["f_ge_one"]["holds"]
    hyp["failed"] = [k for k in mack_keys + ["f_ge_one"] if not hyp[k]["holds"]]
    cert["hypotheses"] = hyp

    # --- numeric instances of the deterministic theorem conclusions on this triangle ---
    tol = 1e-9
    rec_ok = all(abs(se2rec_total(C, f, S, sig2, Chat, i, i) - msep[i]) <= tol * max(1.0, abs(msep[i])) for i in range(n))
    # prod(1+a) - 1 and exp(s) - 1 - s lose about 1e-16 * Chat^2 absolute to cancellation, so the
    # second-order checks use an absolute tolerance scaled by Chat^2 (the identities are exact in R).
    cancel = lambda i: 1e-12 * max(1.0, ult[i] ** 2)
    le_ok = all(per_year[i]["mack"] <= per_year[i]["bbmw"] + cancel(i) for i in range(n))
    bound_ok = all(per_year[i]["bbmw"] - per_year[i]["mack"] <= per_year[i]["bound"] + cancel(i) for i in range(n))
    one_factor_ok = abs(per_year[1]["bbmw"] - per_year[1]["mack"]) <= cancel(1)
    cert["instance_checks"] = dict(
        tolerance_relative=tol, tolerance_absolute_second_order="1e-12 * Chat^2",
        se2rec_eq_msep=dict(holds=rec_ok, applicable=hyp["f_nonzero"]["holds"]),
        mackEstimation_le_bbmwEstimation=dict(holds=le_ok, applicable=hyp["relvar_nonneg"]["holds"]),
        bbmwEstimation_sub_mackEstimation_le=dict(holds=bound_ok, applicable=hyp["relvar_nonneg"]["holds"]),
        bbmwEstimation_eq_mackEstimation_of_one_factor=dict(holds=one_factor_ok, applicable=True),
        process_plus_estimation_eq_total=dict(holds=True, applicable=True),
    )
    for name, chk in cert["instance_checks"].items():
        if isinstance(chk, dict) and chk["applicable"]:
            assert chk["holds"], (name, meta)

    def st(ok, note_ok, note_fail):
        return dict(status="exact theorem" if ok else "hypothesis not met on this triangle", note=note_ok if ok else note_fail)

    boundary = [
        dict(step="f_k is the C_ik-weighted average of the individual factors (fhat_eq_weighted_average)",
             **st(hyp["S_nonzero"]["holds"], "S_k != 0 for all k", f"S_k = 0 in columns {zero_S}")),
        dict(step="Theorem 2: E[f_k^ | D_k] = f_k and E[f_j^ f_k^] = f_j f_k (condExp_fhatRv, condExp_fhatRv_mul)",
             **st(hyp["S_nonzero"]["holds"], "data hypothesis S_k != 0 holds; (M1) and integrability are model assumptions, not testable on one triangle",
                  f"S_k = 0 in columns {zero_S}")),
        dict(step="Theorem 1: E[C^_{i,n-1} | D_d] = E[C_{i,n-1} | D_d] (condExp_ultimate_eq)",
             **st(hyp["S_nonzero"]["holds"], "data hypothesis S_k != 0 for k+2 <= n holds", f"S_k = 0 in columns {zero_S}")),
        dict(step="sigma_k^2 unbiased, k+3 <= n (condExp_sigma2Rv)",
             **st(hyp["S_nonzero"]["holds"] and hyp["C_contributors_nonzero"]["holds"],
                  f"columns 0..{n-3}; column {n-3} has divisor 1", f"C_ik = 0 for {len(zero_contrib_cells)} contributor cells; S_k = 0 in {zero_S}")),
        dict(step="last sigma^2 (column n-2): Mack min-rule extrapolation", status="definition/approximation",
             note="no theorem consumes it; log-linear alternative recorded in last_sigma"),
        dict(step="process variance along a row (condVar_C_eq_procVar)", status="exact theorem",
             note="population form under (M1)-(M3); the plug-in mackProcess is a definition"),
        dict(step="exact conditional MSEP decomposition (condExp_sq_sub_of_stronglyMeasurable, condMsep_eq)", status="exact theorem",
             note="holds for any D-measurable predictor; no data hypothesis"),
        dict(step="Mack's plug-in estimation-error term (mackEstimation)", status="definition/approximation",
             note="conditional-resampling step with cross terms dropped; Chat^2 sum a_k"),
        dict(step="BBMW - Mack = Chat^2 (prod(1+a_k) - 1 - sum a_k) (bbmwEstimation_sub_mackEstimation)", status="exact theorem",
             note="algebraic identity, no hypothesis"),
        dict(step="Mack <= BBMW and second-order bound Chat^2 (exp(sum a) - 1 - sum a) (mackEstimation_le_bbmwEstimation, ..._le)",
             **st(hyp["relvar_nonneg"]["holds"], "a_k >= 0 for all k", f"a_k < 0 in columns {a_neg}")),
        dict(step="Mack 1999 recursion = Mack 1993 closed form (se2rec_eq_msep)",
             **st(hyp["f_nonzero"]["holds"], "f_k != 0 along every row", f"f_k = 0 in columns {[k for k in range(n-1) if f[k]==0]}")),
        dict(step="BF fraction lemma 1 <= cdf (one_le_cdf)",
             **st(hyp["f_ge_one"]["holds"], "f_k >= 1 for all k", f"f_k < 1 in columns {f_below_one}")),
    ]
    cert["approximation_boundary"] = boundary
    return cert


# ----------------------------------------------------------------------------
# Data loading
# ----------------------------------------------------------------------------

def load_line(line):
    path = os.path.join(HERE, "data", f"{line}_pos.csv")
    df = pd.read_csv(path)
    suf = [c for c in df.columns if c.startswith("CumPaidLoss_")][0].split("_", 1)[1]
    col = f"CumPaidLoss_{suf}"
    out = []
    for code, sub in df.groupby("GRCODE", sort=True):
        name = sub["GRNAME"].iloc[0]
        single = int(sub["Single"].iloc[0])
        piv = sub.pivot(index="AccidentYear", columns="DevelopmentLag", values=col)
        assert list(piv.index) == list(range(1988, 1998)) and list(piv.columns) == list(range(1, 11)), (line, code)
        C = [[None] * N for _ in range(N)]
        for i, ay in enumerate(range(1988, 1998)):
            for k in range(N - i):
                v = piv.loc[ay, k + 1]
                assert ay + k <= LAST_CALENDAR_YEAR and not pd.isna(v)
                C[i][k] = float(v)
        out.append((code, name, single, C, suf))
    return out


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        h.update(fh.read())
    return h.hexdigest()


# ----------------------------------------------------------------------------
# Self-test against the two published triangles
# ----------------------------------------------------------------------------

def selftest():
    ta = load_triangle(os.path.join(PARENT, "data", "taylor_ashe_cumulative.csv"))
    raa = load_triangle(os.path.join(PARENT, "case_study", "raa_cumulative.csv"))
    for name, C in [("Taylor-Ashe", ta), ("RAA", raa)]:
        cert = audit_triangle(C, dict(line="selftest", grcode=0, grname=name))
        assert cert["reference_mack_defined"], name
        print(f"selftest {name}: bit-identical to mack(); total reserve {cert['total']['reserve']:,.0f},"
              f" total s.e. {cert['total']['se_mack']:,.0f}, BBMW excess {100*cert['total']['relative_excess']:.3f}%,"
              f" log-linear total s.e. change {100*cert['last_sigma']['loglinear']['rel_change_total_se']:+.2f}%")
    # published checks (Mack 1993 Table 3 total s.e. 13% of 52,135k... use the JSON in ../data)
    pub = json.load(open(os.path.join(PARENT, "data", "mack1993_published_results.json")))
    cert = audit_triangle(ta, dict(line="selftest", grcode=0, grname="Taylor-Ashe"))
    assert round(cert["total"]["reserve"] / 1000) == pub["chain_ladder_reserves_in_thousands"]["overall"]
    assert round(100 * cert["total"]["se_mack"] / cert["total"]["reserve"]) == pub["standard_error_percent_of_reserve"]["overall"]
    raa_pub = json.load(open(os.path.join(PARENT, "case_study", "published_r_chainladder.json")))
    cert = audit_triangle(raa, dict(line="selftest", grcode=0, grname="RAA"))
    assert abs(cert["total"]["se_mack"] - raa_pub["totals"]["Mack.S.E"]) <= 0.005 + 1e-9
    print("selftest: Mack (1993) overall reserve/s.e. and R ChainLadder RAA total Mack.S.E reproduced")


# ----------------------------------------------------------------------------
# Aggregation and reporting
# ----------------------------------------------------------------------------

def pct(x):
    return "" if x is None else f"{100*x:.2f}"


def fmt_dist(d, scale=100.0, nd=2):
    if d.get("n", 0) == 0:
        return " & ".join(["0"] + ["--"] * 6)
    return " & ".join([str(d["n"])] + [f"{scale*d[k]:.{nd}f}" for k in ["min", "q1", "median", "mean", "q3", "max"]])


def md_dist_row(label, d, scale=100.0, nd=2):
    if d.get("n", 0) == 0:
        return f"| {label} | 0 | | | | | | |"
    return f"| {label} | {d['n']} | " + " | ".join(f"{scale*d[k]:.{nd}f}" for k in ["min", "q1", "median", "mean", "q3", "max"]) + " |"


def aggregate(certs):
    groups = defaultdict(list)
    for c in certs:
        groups[c["line"]].append(c)
    groups["overall"] = list(certs)
    order = [l for l, _ in LINES] + ["overall"]
    agg = {}
    for g in order:
        cs = groups[g]
        aud = [c for c in cs if c["status"] == "audited"]
        clean = [c for c in aud if c["hypotheses"]["all_mack_data_hypotheses_hold"]]
        clean_bf = [c for c in aud if c["hypotheses"]["all_data_hypotheses_including_bf_hold"]]
        skipped = [c for c in cs if c["status"] == "skipped"]
        fail_counts = Counter()
        for c in aud:
            for k in c["hypotheses"]["failed"]:
                fail_counts[k] += 1
        skip_reasons = Counter(("all_zero" if c["skip_reason"].startswith("all") else
                                f"nonzero_latest_diagonal_years={c['structural']['accident_years_with_nonzero_latest_diagonal']}") for c in skipped)

        def dist_over(cs_, key):
            return quantiles([key(c) for c in cs_])

        def counts_over(cs_, key, thresholds=(0.01, 0.05, 0.10)):
            vals = [key(c) for c in cs_]
            vals = [v for v in vals if v is not None and math.isfinite(v)]
            return {f"gt_{int(100*t)}pct": sum(1 for v in vals if v > t) for t in thresholds} | dict(n=len(vals))

        rel = lambda c: c["total"]["relative_excess"]
        maxa = lambda c: c["relvar"]["max_a"]
        share = lambda c: c["total"]["estimation_share_of_msep"]
        llrel = lambda c: (c["last_sigma"]["loglinear"] or {}).get("rel_change_total_se")
        llabs = lambda c: (abs(llrel(c)) if llrel(c) is not None else None)
        lldef = lambda c: (c["last_sigma"]["loglinear"] or {}).get("rel_change_total_se_package_default")
        lldefabs = lambda c: (abs(lldef(c)) if lldef(c) is not None else None)
        suma = lambda c: c["relvar"]["sum_a_youngest_row"]
        maxyear = lambda c: max((y["relative_excess"] for y in c["per_accident_year"] if y["relative_excess"] is not None), default=None)
        bound_ratio = lambda c: (c["total"]["difference"] / c["total"]["second_order_bound"]) if c["total"]["second_order_bound"] > 0 else None

        entry = dict(
            label=LINE_LABEL.get(g, "All six lines"),
            companies=len(cs), audited=len(aud), skipped=len(skipped), skip_reasons=dict(skip_reasons),
            all_mack_data_hypotheses_hold=len(clean), all_data_hypotheses_including_bf_hold=len(clean_bf),
            hypothesis_failures=dict(fail_counts),
            n_reference_mack_undefined=sum(1 for c in aud if not c["reference_mack_defined"]),
        )
        defined = [c for c in aud if all(c["hypotheses"][k]["holds"] for k in ["S_nonzero", "f_nonzero", "latest_diagonal_nonzero"])]
        entry["chain_ladder_defined"] = len(defined)
        entry["reference_mack_defined"] = sum(1 for c in aud if c["reference_mack_defined"])
        entry["clean_but_reference_mack_raises"] = sum(1 for c in clean if not c["reference_mack_defined"])
        entry["negative_cell_triangles"] = sum(1 for c in aud if c["structural"]["negative_cells"] > 0)
        entry["zero_estimable_sigma_triangles"] = sum(1 for c in aud if c["sigma2"]["zero_estimable_columns"])
        entry["zero_estimable_sigma_triangles_clean"] = sum(1 for c in clean if c["sigma2"]["zero_estimable_columns"])
        entry["min_rule_branch_clean"] = dict(Counter(c["last_sigma"]["min_rule_branch"] for c in clean))
        entry["argmax_a_clean"] = dict(Counter(c["relvar"]["argmax_a"] for c in clean))
        entry["sets"] = {}
        for setname, cs_ in [("clean", clean), ("defined", defined), ("audited", aud)]:
            entry["sets"][setname] = dict(
                relative_excess_total=dist_over(cs_, rel),
                relative_excess_total_counts=counts_over(cs_, rel),
                relative_excess_max_single_year=dist_over(cs_, maxyear),
                max_a=dist_over(cs_, maxa),
                sum_a_youngest_row=dist_over(cs_, suma),
                estimation_share_of_msep=dist_over(cs_, share),
                loglinear_rel_change_total_se=dist_over(cs_, llrel),
                loglinear_abs_rel_change_counts=counts_over(cs_, llabs),
                loglinear_package_default_rel_change=dist_over(cs_, lldef),
                loglinear_package_default_abs_counts=counts_over(cs_, lldefabs),
                loglinear_undefined=sum(1 for c in cs_ if c["last_sigma"]["loglinear"] is None),
                package_default_picks_loglinear=sum(1 for c in cs_ if (c["last_sigma"]["loglinear"] or {}).get("chainladder_default_uses") == "log-linear"),
                remainder_over_bound=dist_over(cs_, bound_ratio),
                relative_excess_undefined=sum(1 for c in cs_ if rel(c) is None),
            )
        agg[g] = entry
    return agg, order


def write_tables(agg, order, certs):
    md, tex = [], []
    # Table 1: counts
    md.append("### Table 1. Triangles, audits, hypothesis status, and threshold counts\n")
    md.append("Excess = (BBMW - Mack)/Mack of the total estimation-error term (cross terms included). LL = |relative change in total Mack S.E.| when the last sigma is extrapolated log-linearly instead of by the min-rule. Counts on the data-clean set.\n")
    md.append("| Line | Companies | Audited | Skipped | CL defined | All Mack data hyps | + BF f>=1 | Excess >1% | >5% | >10% | LL >1% | >5% | >10% | LL default >1% | >5% | >10% |")
    md.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    tex.append("% Table 1: counts (line & companies & audited & skipped & CL defined & all Mack data hypotheses & incl. BF & excess>1% & >5% & >10% & LL>1% & >5% & >10% & LL default >1% & >5% & >10%)")
    for g in order:
        e = agg[g]
        rc, lc = e["sets"]["clean"]["relative_excess_total_counts"], e["sets"]["clean"]["loglinear_abs_rel_change_counts"]
        dc = e["sets"]["clean"]["loglinear_package_default_abs_counts"]
        cells = [e["label"] if g != "overall" else "All lines", e["companies"], e["audited"], e["skipped"], e["chain_ladder_defined"], e["all_mack_data_hypotheses_hold"], e["all_data_hypotheses_including_bf_hold"],
                 rc["gt_1pct"], rc["gt_5pct"], rc["gt_10pct"], lc["gt_1pct"], lc["gt_5pct"], lc["gt_10pct"], dc["gt_1pct"], dc["gt_5pct"], dc["gt_10pct"]]
        md.append("| " + " | ".join(str(x) for x in cells) + " |")
        tex.append(" & ".join(str(x) for x in cells) + " \\\\" + ("\\midrule" if g == "othliab" else ""))
    md.append("")
    # Distribution tables
    dists = [
        ("relative_excess_total", "Table 2. Relative excess (BBMW - Mack)/Mack of the total estimation-error term, percent", 100.0, 3),
        ("max_a", "Table 3. Largest relative estimation variance max_k a_k, percent", 100.0, 3),
        ("estimation_share_of_msep", "Table 4. Estimation-error share of total Mack MSEP, percent", 100.0, 1),
        ("loglinear_rel_change_total_se", "Table 5. Relative change in total Mack S.E., log-linear last sigma versus min-rule, percent (signed)", 100.0, 1),
        ("loglinear_package_default_rel_change", "Table 6. Same as Table 5 under the ChainLadder default (log-linear only if slope p <= 0.05, else min-rule), percent", 100.0, 1),
        ("relative_excess_max_single_year", "Table 7. Largest single-accident-year relative excess (BBMW - Mack)/Mack, percent", 100.0, 2),
    ]
    for key, title, scale, nd in dists:
        md.append(f"### {title}\n")
        md.append("Data-clean triangles.\n")
        md.append("| Line | N | min | Q1 | median | mean | Q3 | max |")
        md.append("|---|---|---|---|---|---|---|---|")
        tex.append(f"% {title} (line & N & min & Q1 & median & mean & Q3 & max), data-clean set")
        for g in order:
            e = agg[g]
            d = e["sets"]["clean"][key]
            md.append(md_dist_row(e["label"] if g != "overall" else "All lines", d, scale, nd))
            tex.append((e["label"] if g != "overall" else "All lines") + " & " + fmt_dist(d, scale, nd) + " \\\\" + ("\\midrule" if g == "othliab" else ""))
        md.append("")
        md.append("Triangles on which the chain ladder is defined (S_k != 0, f_k != 0, nonzero latest diagonal); negative cells, a_k < 0, f_k < 1 and zero contributor cells allowed:\n")
        md.append("| Line | N | min | Q1 | median | mean | Q3 | max |")
        md.append("|---|---|---|---|---|---|---|---|")
        for g in order:
            e = agg[g]
            md.append(md_dist_row(e["label"] if g != "overall" else "All lines", e["sets"]["defined"][key], scale, nd))
        md.append("")
    # hypothesis failure table
    md.append("### Table 8. Hypothesis failures among audited triangles (a triangle can fail several)\n")
    keys = ["cells_nonneg", "S_nonzero", "C_contributors_nonzero", "latest_diagonal_nonzero", "f_nonzero", "relvar_nonneg", "sigma_df", "f_ge_one"]
    md.append("| Line | Audited | " + " | ".join(keys) + " |")
    md.append("|---|---|" + "---|" * len(keys))
    tex.append("% Table 8: hypothesis failures (line & audited & " + " & ".join(keys) + ")")
    for g in order:
        e = agg[g]
        cells = [e["label"] if g != "overall" else "All lines", e["audited"]] + [e["hypothesis_failures"].get(k, 0) for k in keys]
        md.append("| " + " | ".join(str(x) for x in cells) + " |")
        tex.append(" & ".join(str(x) for x in cells) + " \\\\" + ("\\midrule" if g == "othliab" else ""))
    md.append("")
    md.append("### Table 9. Skip reasons\n")
    md.append("| Line | Skipped | Reason: all zero | Reason: fewer than 3 nonzero latest-diagonal years |")
    md.append("|---|---|---|---|")
    for g in order:
        e = agg[g]
        cs = [c for c in certs if c["status"] == "skipped" and (g == "overall" or c["line"] == g)]
        allz = sum(1 for c in cs if c["skip_reason"].startswith("all"))
        md.append(f"| {e['label'] if g != 'overall' else 'All lines'} | {len(cs)} | {allz} | {len(cs)-allz} |")
    md.append("")
    # top excess triangles
    md.append("### Table 10. Ten data-clean triangles with the largest total relative excess\n")
    md.append("| Line | GRCODE | Company | Reserve | Excess % | max a_k % | argmax k | Total S.E. ratio (BBMW/Mack) |")
    md.append("|---|---|---|---|---|---|---|---|")
    clean = [c for c in certs if c["status"] == "audited" and c["hypotheses"]["all_mack_data_hypotheses_hold"] and c["total"]["relative_excess"] is not None]
    for c in sorted(clean, key=lambda c: -c["total"]["relative_excess"])[:10]:
        md.append(f"| {c['line']} | {c['grcode']} | {c['grname']} | {c['total']['reserve']:,.0f} | {100*c['total']['relative_excess']:.2f} | {100*c['relvar']['max_a']:.2f} | {c['relvar']['argmax_a']} | {c['total']['se_ratio_bbmw_over_mack']:.4f} |")
    md.append("")
    return "\n".join(md), "\n".join(tex)


def main():
    if "--selftest" in sys.argv:
        selftest()
        return 0
    selftest()
    os.makedirs(os.path.join(HERE, "certificates"), exist_ok=True)
    for old in glob.glob(os.path.join(HERE, "certificates", "*.json")):
        os.remove(old)
    certs = []
    dataset = {}
    duplicates = []
    for line, label in LINES:
        path = os.path.join(HERE, "data", f"{line}_pos.csv")
        rows = load_line(line)
        seen = {}
        for code, name, single, C, suf in rows:
            key = tuple(tuple(x for x in r if x is not None) for r in C)
            if key in seen and any(v != 0 for r in key for v in r):
                duplicates.append(dict(line=line, grcode=code, grname=name, same_as_grcode=seen[key][0], same_as_grname=seen[key][1]))
            seen.setdefault(key, (code, name))
            cert = audit_triangle(C, dict(line=line, line_label=label, grcode=int(code), grname=name, single=single,
                                          column=f"CumPaidLoss_{suf}", triangle_upper=[[x for x in r if x is not None] for r in C]))
            certs.append(cert)
            with open(os.path.join(HERE, "certificates", f"{line}_{code}.json"), "w") as fh:
                json.dump(cert, fh, indent=1)
        dataset[line] = dict(file=os.path.basename(path), sha256=sha256(path), companies=len(rows), cumulative_paid_column=f"CumPaidLoss_{rows[0][4]}")
        print(f"{line}: {len(rows)} companies, {sum(1 for c in certs if c['line']==line and c['status']=='audited')} audited")
    agg, order = aggregate(certs)
    md_tables, tex = write_tables(agg, order, certs)
    summary = dict(
        generated="2026-08-25", n=N, calendar_year_cutoff=LAST_CALENDAR_YEAR, accident_years=[1988, 1997],
        dataset=dataset, duplicate_triangles=duplicates, aggregate=agg,
        certificates=len(certs),
    )
    with open(os.path.join(HERE, "summary.json"), "w") as fh:
        json.dump(summary, fh, indent=1)
    with open(os.path.join(HERE, "tables.tex"), "w") as fh:
        fh.write(tex + "\n")
    with open(os.path.join(HERE, "aggregate_tables.md"), "w") as fh:
        fh.write(md_tables)
    findings_path = os.path.join(HERE, "FINDINGS.md")
    if not os.path.isfile(findings_path):
        raise FileNotFoundError(
            "scripts/audit/FINDINGS.md is required to regenerate AUDIT_RESULTS.md"
        )
    with open(findings_path) as fh:
        findings = fh.read()
    with open(os.path.join(HERE, "AUDIT_RESULTS.md"), "w") as fh:
        fh.write("# Theorem-aware reserving audit: CAS Schedule P database, cumulative paid, year-end 1997\n\n")
        fh.write("`audit.py` writes this report (one command: `./run.sh`). Certificates per company are in `certificates/<line>_<GRCODE>.json`; "
                 "machine-readable aggregates in `summary.json`; LaTeX table bodies in `tables.tex`; sources and hashes in `SOURCES.md`.\n\n")
        fh.write("Dataset: " + ", ".join(f"{l} {dataset[l]['companies']}" for l, _ in LINES) + f" companies ({sum(d['companies'] for d in dataset.values())} total). ")
        fh.write(f"Audited {agg['overall']['audited']}, skipped {agg['overall']['skipped']} (degenerate). "
                 f"All audited Mack data hypotheses hold on {agg['overall']['all_mack_data_hypotheses_hold']}; adding the BF lemma's data-side condition f_k >= 1, on {agg['overall']['all_data_hypotheses_including_bf_hold']}.\n\n")
        fh.write("## Findings\n\n" + findings.strip() + "\n\n## Aggregate tables\n\n" + md_tables + "\n")
        if duplicates:
            fh.write("## Duplicate triangles within a line (identical 55 upper cells, not all zero)\n\n")
            for d in duplicates:
                fh.write(f"- {d['line']}: GRCODE {d['grcode']} ({d['grname']}) equals GRCODE {d['same_as_grcode']} ({d['same_as_grname']})\n")
    print(f"wrote {len(certs)} certificates, summary.json, tables.tex, aggregate_tables.md, AUDIT_RESULTS.md")
    o = agg["overall"]
    print(f"overall: audited {o['audited']}, CL defined {o['chain_ladder_defined']}, mack() defined {o['reference_mack_defined']}, data-clean {o['all_mack_data_hypotheses_hold']}, excess>1% {o['sets']['clean']['relative_excess_total_counts']}, LL {o['sets']['clean']['loglinear_abs_rel_change_counts']}, LL default {o['sets']['clean']['loglinear_package_default_abs_counts']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
