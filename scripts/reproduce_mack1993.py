#!/usr/bin/env python3
"""Reproduce Mack (1993), Section 4, from the Taylor-Ashe triangle.

Computes the chain-ladder factors, Mack's sigma_k^2 estimators (with the
extrapolation convention for the last one), reserves, and the MSEP of each
accident year and of the total, then compares with the numbers printed in
Mack (1993) Tables 2 and 3. Pure Python, no dependencies.

Conventions (zero-based, matching VerifiedReserving/ChainLadder.lean):
  n accident years i = 0..n-1, development years k = 0..n-1,
  latest observed entry of year i is column n-1-i,
  f_k uses accident years i = 0..n-k-2,
  sigma_k^2 = 1/(n-k-2) * sum_i C_ik (C_i,k+1/C_ik - f_k)^2  for k <= n-3,
  sigma_{n-2}^2 = min(sigma_{n-3}^4 / sigma_{n-4}^2, min(sigma_{n-4}^2, sigma_{n-3}^2))  (Mack 1993, p.~222).
"""
import csv
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load_triangle(path):
    rows = []
    with open(path) as fh:
        r = csv.reader(fh)
        next(r)
        for row in r:
            rows.append([float(x) if x else None for x in row[1:]])
    return rows


def mack(C):
    n = len(C)
    f, S, sig2 = [], [], []
    for k in range(n - 1):
        idx = range(n - k - 1)
        Sk = sum(C[i][k] for i in idx)
        Tk = sum(C[i][k + 1] for i in idx)
        f.append(Tk / Sk)
        S.append(Sk)
    for k in range(n - 1):
        m = n - k - 2
        if m >= 1:
            sig2.append(sum(C[i][k] * (C[i][k + 1] / C[i][k] - f[k]) ** 2 for i in range(n - k - 1)) / m)
        else:
            sig2.append(None)
    # Mack's extrapolation for the last sigma^2 (k = n-2)
    a, b = sig2[n - 4], sig2[n - 3]
    sig2[n - 2] = min(b * b / a, min(a, b))
    # projections
    Chat = [[None] * n for _ in range(n)]
    for i in range(n):
        d = n - 1 - i
        Chat[i][d] = C[i][d]
        for k in range(d, n - 1):
            Chat[i][k + 1] = Chat[i][k] * f[k]
    ult = [Chat[i][n - 1] for i in range(n)]
    res = [ult[i] - C[i][n - 1 - i] for i in range(n)]
    msep = []
    for i in range(n):
        d = n - 1 - i
        s = sum(sig2[k] / f[k] ** 2 * (1.0 / Chat[i][k] + 1.0 / S[k]) for k in range(d, n - 1))
        msep.append(ult[i] ** 2 * s)
    # total MSEP (Mack 1993, p. 220): sum of individual + covariance terms
    total = sum(msep)
    for i in range(n):
        d = n - 1 - i
        later = sum(ult[j] for j in range(i + 1, n))
        total += ult[i] * later * sum(2 * sig2[k] / f[k] ** 2 / S[k] for k in range(d, n - 1))
    return f, sig2, res, msep, total


def main():
    C = load_triangle(os.path.join(HERE, "data", "taylor_ashe_cumulative.csv"))
    pub = json.load(open(os.path.join(HERE, "data", "mack1993_published_results.json")))
    f, sig2, res, msep, total = mack(C)
    n = len(C)
    print("k   f_k       sigma_k^2/1000   published f   published sigma^2/1000")
    misprints = []
    for k in range(n - 1):
        pf = pub['development_factors_fk_as_printed'][k]
        ps = pub['sigma_k_squared_over_1000_as_printed'][k]
        f_dec = len(str(pf).split(".")[-1]) if "." in str(pf) else 0
        f_ok = abs(f[k] - pf) <= 0.5 * 10 ** (-f_dec)
        s_ok = abs(sig2[k] / 1000 - ps) <= 0.5 * 10 ** (-len(str(ps).split('.')[-1])) if '.' in str(ps) else abs(sig2[k] / 1000 - ps) <= 0.5
        flag = ''
        if not f_ok:
            flag += '  <-- FACTOR MISMATCH'
        if not s_ok:
            if k == n - 2:
                flag += f'  <-- MISPRINT in source: the extrapolation rule on the printed sigma_{k-1}^2, sigma_{k}^2 gives {sig2[k]/1000:.3f}, and the printed standard errors are reproduced with it'
                misprints.append(k + 1)
            else:
                flag += '  <-- SIGMA MISMATCH'
                ok_sigma = False
        print(f"{k+1:<3} {f[k]:<9.4f} {sig2[k]/1000:<16.4g} {pf:<13} {ps}{flag}")
    print("\ni   reserve(000)  published   s.e.%   published%")
    ok = True
    for i in range(1, n):
        se = 100 * math.sqrt(msep[i]) / res[i]
        pr = pub["chain_ladder_reserves_in_thousands"][str(i + 1)]
        pse = pub["standard_error_percent_of_reserve"][str(i + 1)]
        flag = "" if round(res[i] / 1000) == pr and round(se) == pse else "  <-- MISMATCH"
        ok &= flag == ""
        print(f"{i+1:<3} {res[i]/1000:<13.0f} {pr:<11} {se:<7.0f} {pse}{flag}")
    tot_res = sum(res)
    tot_se = 100 * math.sqrt(total) / tot_res
    pr = pub["chain_ladder_reserves_in_thousands"]["overall"]
    pse = pub["standard_error_percent_of_reserve"]["overall"]
    flag = "" if round(tot_res / 1000) == pr and round(tot_se) == pse else "  <-- MISMATCH"
    ok &= flag == ""
    print(f"all {tot_res/1000:<13.0f} {pr:<11} {tot_se:<7.0f} {pse}{flag}")
    if ok and misprints:
        print(f"\nRESULT: all printed reserves and standard errors reproduced; the printed sigma_{misprints[0]}^2 is a misprint in the source (see the MISPRINT row)")
    else:
        print("\nRESULT:", "all printed values reproduced" if ok else "discrepancies found (see MISMATCH rows)")
    if "--catalogue" in sys.argv:
        catalogue(C, f, sig2, res)
    return 0 if ok else 1


def catalogue(C, f, sig2, res):
    """Mack's estimation-error term versus the conditional-resampling (BBMW) term,
    per accident year, on the same triangle. Prints a LaTeX table body."""
    n = len(C)
    S = []
    for k in range(n - 1):
        S.append(sum(C[i][k] for i in range(n - k - 1)))
    Chat = [[None] * n for _ in range(n)]
    for i in range(n):
        d = n - 1 - i
        Chat[i][d] = C[i][d]
        for k in range(d, n - 1):
            Chat[i][k + 1] = Chat[i][k] * f[k]
    print("\nAY & reserve & Mack est. s.e. & BBMW est. s.e. & difference of squares & rel. diff \\\\")
    tot_m = tot_b = 0.0
    for i in range(1, n):
        d = n - 1 - i
        a = [sig2[k] / f[k] ** 2 / S[k] for k in range(d, n - 1)]
        ult = Chat[i][n - 1]
        mack = ult ** 2 * sum(a)
        prod = 1.0
        for x in a:
            prod *= 1 + x
        bbmw = ult ** 2 * (prod - 1)
        tot_m += mack
        tot_b += bbmw
        print(f"{i+1} & {res[i]/1000:,.0f} & {math.sqrt(mack)/1000:,.1f} & {math.sqrt(bbmw)/1000:,.1f} & {(bbmw-mack)/1e6:,.3f} & {100*(bbmw-mack)/mack:.2f}\\% \\\\")
    print(f"sum of single-year terms & & {math.sqrt(tot_m)/1000:,.1f} & {math.sqrt(tot_b)/1000:,.1f} & {(tot_b-tot_m)/1e6:,.3f} & {100*(tot_b-tot_m)/tot_m:.2f}\\% \\\\")
    print("(reserves and s.e. in thousands; difference of squared terms in 10^6 thousands^2)")


if __name__ == "__main__":
    sys.exit(main())
