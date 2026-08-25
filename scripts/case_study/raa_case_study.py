#!/usr/bin/env python3
"""RAA case study: formalized Mack chain-ladder definitions versus the published
R ChainLadder output, and Mack's estimation-error term versus the
conditional-resampling (BBMW) term.

Exhibit 1: per accident year and total, published R value (MackChainLadder(RAA,
           est.sigma="Mack") as printed in the ChainLadder vignette), our value
           from the formalized definitions (imported from ../reproduce_mack1993.py),
           and the difference, for Ultimate, IBNR and Mack S.E.
Exhibit 2: per accident year, Mack's estimation-error term
           Chat_i^2 * sum_k sigma_k^2 / (f_k^2 S_k)
           versus the conditional-resampling term
           Chat_i^2 * (prod_k (1 + sigma_k^2 / (f_k^2 S_k)) - 1)
           and their difference.
Diagnosis: the last-sigma rule. Mack's min-rule (used by mack()) versus the
           ChainLadder default log-linear rule, and which one reproduces R.

Usage: python3 raa_case_study.py            (prints exhibits + LaTeX bodies)
       python3 raa_case_study.py --json     (also writes raa_case_study_results.json)
Pure Python except scipy.stats.linregress for the log-linear p-value.
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from reproduce_mack1993 import load_triangle, mack  # noqa: E402  (same formulas as the Lean definitions)

ORIGINS = list(range(1981, 1991))


def basics(C):
    """f_k, S_k and the estimable sigma_k^2 (k <= n-3), zero-based, same formulas as mack()."""
    n = len(C)
    f, S, sig2 = [], [], []
    for k in range(n - 1):
        idx = range(n - k - 1)
        Sk = sum(C[i][k] for i in idx)
        f.append(sum(C[i][k + 1] for i in idx) / Sk)
        S.append(Sk)
    for k in range(n - 1):
        m = n - k - 2
        sig2.append(sum(C[i][k] * (C[i][k + 1] / C[i][k] - f[k]) ** 2 for i in range(n - k - 1)) / m if m >= 1 else None)
    return f, S, sig2


def last_sigma_mack(sig2):
    """Mack (1993) p. 222 min-rule, identical to the line in mack()."""
    n = len(sig2) + 1
    a, b = sig2[n - 4], sig2[n - 3]
    return min(b * b / a, min(a, b))


def last_sigma_loglinear(sig2):
    """ChainLadder estimate.sigma(): lm(log(sigma_k) ~ k) over the estimable k with
    sigma_k > 0, extrapolated to the last k. Returns (sigma_last^2, slope p-value)."""
    from scipy.stats import linregress
    n = len(sig2) + 1
    ks = [k + 1 for k in range(n - 1) if sig2[k] is not None and sig2[k] > 0]  # R uses dev = 1..n
    ys = [math.log(math.sqrt(sig2[k - 1])) for k in ks]
    fit = linregress(ks, ys)
    pred = math.exp(fit.intercept + fit.slope * (n - 1))
    return pred * pred, fit.pvalue


def project(C, f):
    n = len(C)
    Chat = [[None] * n for _ in range(n)]
    for i in range(n):
        d = n - 1 - i
        Chat[i][d] = C[i][d]
        for k in range(d, n - 1):
            Chat[i][k + 1] = Chat[i][k] * f[k]
    return Chat


def msep_with_sigma(C, f, S, sig2):
    """Mack's per-year MSEP and total MSEP for a given full sigma^2 vector; same
    formulas as mack(), factored out so the last-sigma rule can be swapped."""
    n = len(C)
    Chat = project(C, f)
    ult = [Chat[i][n - 1] for i in range(n)]
    msep = []
    for i in range(n):
        d = n - 1 - i
        s = sum(sig2[k] / f[k] ** 2 * (1.0 / Chat[i][k] + 1.0 / S[k]) for k in range(d, n - 1))
        msep.append(ult[i] ** 2 * s)
    total = sum(msep)
    for i in range(n):
        d = n - 1 - i
        later = sum(ult[j] for j in range(i + 1, n))
        total += ult[i] * later * sum(2 * sig2[k] / f[k] ** 2 / S[k] for k in range(d, n - 1))
    return ult, msep, total


def estimation_error_terms(C, f, S, sig2):
    """Per year: Mack's estimation-error term and the conditional-resampling term."""
    n = len(C)
    Chat = project(C, f)
    out = []
    for i in range(n):
        d = n - 1 - i
        a = [sig2[k] / f[k] ** 2 / S[k] for k in range(d, n - 1)]
        ult = Chat[i][n - 1]
        m = ult ** 2 * sum(a)
        p = 1.0
        for x in a:
            p *= 1 + x
        out.append((m, ult ** 2 * (p - 1)))
    return out


def fmt(x, nd=0):
    return f"{x:,.{nd}f}"


def main():
    C = load_triangle(os.path.join(HERE, "raa_cumulative.csv"))
    pub = json.load(open(os.path.join(HERE, "published_r_chainladder.json")))
    n = len(C)

    # --- reference calculation: exactly mack() from reproduce_mack1993.py (min-rule) ---
    f, sig2, res, msep, total = mack(C)
    f2, S, sig2_est = basics(C)
    assert f2 == f
    ult, msep2, total2 = msep_with_sigma(C, f, S, sig2)
    assert msep2 == msep and total2 == total, "factored MSEP must equal mack() bit for bit"
    latest = [C[i][n - 1 - i] for i in range(n)]

    print("=" * 78)
    print("RAA triangle: chain-ladder factors and sigma_k^2 (our calculation)")
    print("=" * 78)
    print("k   f_k       Mack1994 f_k   sigma_k^2      Mack1994 alpha_k^2")
    pa = pub["mack1994_p130_alpha_k_squared_as_printed"]
    pf = pub["mack1994_p126_f_k_as_printed"]
    for k in range(n - 1):
        print(f"{k+1:<3} {f[k]:<9.3f} {pf[k]:<14} {sig2[k]:<14.4g} {pa[k]}")
    ll2, pval = last_sigma_loglinear(sig2_est)
    print(f"\nlast sigma^2 (k={n-1}): Mack min-rule = {last_sigma_mack(sig2_est):.4g};"
          f" ChainLadder log-linear = {ll2:.4g} (slope p-value {pval:.4f};"
          f" {'used' if pval <= 0.05 else 'NOT used, falls back to Mack rule'} by the package default)")
    print(f"Mack 1994 p.130 quotes the log-linear extrapolation as exp(-0.44) = 0.64 and the min-rule as 1.34.")

    # --- Exhibit 1 ---
    print("\n" + "=" * 78)
    print("Exhibit 1: published R ChainLadder (est.sigma='Mack') vs formalized definitions")
    print("=" * 78)
    hdr = f"{'AY':<6}{'Ult (R)':>11}{'Ult (ours)':>13}{'diff':>9}{'IBNR (R)':>11}{'IBNR (ours)':>13}{'diff':>9}{'S.E. (R)':>11}{'S.E. (ours)':>13}{'diff':>9}"
    print(hdr)
    rows = []
    maxabs = {"Ultimate": 0.0, "IBNR": 0.0, "Mack.S.E": 0.0}
    for i, o in enumerate(ORIGINS):
        p = pub["by_origin"][str(o)]
        se = math.sqrt(msep[i])
        d_u, d_r, d_s = ult[i] - p["Ultimate"], res[i] - p["IBNR"], se - p["Mack.S.E"]
        maxabs["Ultimate"] = max(maxabs["Ultimate"], abs(d_u))
        maxabs["IBNR"] = max(maxabs["IBNR"], abs(d_r))
        maxabs["Mack.S.E"] = max(maxabs["Mack.S.E"], abs(d_s))
        rows.append(dict(origin=o, latest=latest[i], ult_R=p["Ultimate"], ult=ult[i], ibnr_R=p["IBNR"], ibnr=res[i], se_R=p["Mack.S.E"], se=se))
        print(f"{o:<6}{fmt(p['Ultimate']):>11}{fmt(ult[i], 1):>13}{d_u:>9.2f}{fmt(p['IBNR']):>11}{fmt(res[i], 1):>13}{d_r:>9.2f}{fmt(p['Mack.S.E']):>11}{fmt(se, 1):>13}{d_s:>9.2f}")
    T = pub["totals"]
    tu, tr, ts = sum(ult), sum(res), math.sqrt(total)
    print(f"{'Total':<6}{fmt(T['Ultimate'], 2):>11}{fmt(tu, 2):>13}{tu-T['Ultimate']:>9.2f}{fmt(T['IBNR'], 2):>11}{fmt(tr, 2):>13}{tr-T['IBNR']:>9.2f}{fmt(T['Mack.S.E'], 2):>11}{fmt(ts, 2):>13}{ts-T['Mack.S.E']:>9.2f}")
    print(f"\nmax |difference| per year (R prints integers, so <= 0.5 is rounding): "
          f"Ultimate {maxabs['Ultimate']:.3f}, IBNR {maxabs['IBNR']:.3f}, Mack S.E. {maxabs['Mack.S.E']:.3f}")
    print(f"totals (R prints 2 decimals): Ultimate {tu-T['Ultimate']:+.4f}, IBNR {tr-T['IBNR']:+.4f}, S.E. {ts-T['Mack.S.E']:+.4f}")
    match_mack = maxabs["Mack.S.E"] <= 0.5 and abs(ts - T["Mack.S.E"]) <= 0.005 + 1e-9

    # --- same triangle under the log-linear last sigma (ChainLadder default) ---
    sig2_ll = list(sig2_est)
    sig2_ll[n - 2] = ll2
    ult_ll, msep_ll, total_ll = msep_with_sigma(C, f, S, sig2_ll)
    print("\nSame triangle with the ChainLadder default log-linear last sigma (what MackChainLadder(RAA) prints with no est.sigma argument):")
    print(f"{'AY':<6}{'S.E. min-rule':>15}{'S.E. log-linear':>17}{'diff':>10}")
    ll_rows = []
    for i, o in enumerate(ORIGINS):
        a, b = math.sqrt(msep[i]), math.sqrt(msep_ll[i])
        ll_rows.append(dict(origin=o, se_mack_rule=a, se_loglinear=b))
        print(f"{o:<6}{fmt(a, 1):>15}{fmt(b, 1):>17}{b-a:>10.2f}")
    print(f"{'Total':<6}{fmt(ts, 2):>15}{fmt(math.sqrt(total_ll), 2):>17}{math.sqrt(total_ll)-ts:>10.2f}")
    print("(every year's projection passes through f_9, so every s.e. moves; the effect is largest for 1982, whose MSEP is the f_9 term alone)")

    # --- Exhibit 2 ---
    print("\n" + "=" * 78)
    print("Exhibit 2: Mack estimation-error term vs conditional-resampling (BBMW) term")
    print("=" * 78)
    terms = estimation_error_terms(C, f, S, sig2)
    print(f"{'AY':<6}{'IBNR':>9}{'Mack est. s.e.':>16}{'resampl. est. s.e.':>20}{'diff of squares':>17}{'rel. diff':>11}{'share of MSEP':>15}")
    ex2 = []
    tot_m = tot_b = 0.0
    for i, o in enumerate(ORIGINS):
        m, b = terms[i]
        if i == 0:
            continue
        tot_m += m
        tot_b += b
        ex2.append(dict(origin=o, ibnr=res[i], mack_term=m, resampling_term=b, diff=b - m, rel=(b - m) / m, share_of_msep=(b - m) / msep[i]))
        print(f"{o:<6}{fmt(res[i]):>9}{fmt(math.sqrt(m), 1):>16}{fmt(math.sqrt(b), 1):>20}{fmt(b-m, 1):>17}{100*(b-m)/m:>10.3f}%{100*(b-m)/msep[i]:>14.3f}%")
    print(f"{'Sum':<6}{fmt(tr):>9}{fmt(math.sqrt(tot_m), 1):>16}{fmt(math.sqrt(tot_b), 1):>20}{fmt(tot_b-tot_m, 1):>17}{100*(tot_b-tot_m)/tot_m:>10.3f}%")
    print("(s.e. columns are square roots of the single-year estimation-error terms only, not the full MSEP;")
    print(" 'share of MSEP' = difference of squared terms divided by the year's full Mack MSEP; sum row adds single-year terms without cross terms)")

    # --- total-level comparison: Mack's total MSEP vs the resampling analogue ---
    # BBMW total estimation error: sum_{i,j} Chat_i Chat_j (prod_{k>=min-diag} (1+a_k) - 1) over the common factors.
    Chat = project(C, f)
    a_k = [sig2[k] / f[k] ** 2 / S[k] for k in range(n - 1)]
    tot_est_mack = tot_est_bbmw = 0.0
    for i in range(1, n):
        for j in range(1, n):
            d = max(n - 1 - i, n - 1 - j)  # both years use f_k for k >= d
            common = a_k[d:]
            p = 1.0
            for x in common:
                p *= 1 + x
            tot_est_mack += ult[i] * ult[j] * sum(common)
            tot_est_bbmw += ult[i] * ult[j] * (p - 1)
    proc_total = sum(ult[i] ** 2 * sum(sig2[k] / f[k] ** 2 / Chat[i][k] for k in range(n - 1 - i, n - 1)) for i in range(1, n))
    assert abs(proc_total + tot_est_mack - total) < 1e-6 * total
    print(f"\nTotal reserve: process variance {proc_total:,.0f}; estimation error Mack {tot_est_mack:,.0f} vs resampling {tot_est_bbmw:,.0f}"
          f" (diff {tot_est_bbmw-tot_est_mack:,.0f}, {100*(tot_est_bbmw-tot_est_mack)/tot_est_mack:.3f}% of Mack's term,"
          f" {100*(tot_est_bbmw-tot_est_mack)/total:.3f}% of total MSEP)")
    print(f"Total s.e.: Mack {math.sqrt(total):,.2f} vs with resampling estimation error {math.sqrt(proc_total+tot_est_bbmw):,.2f}")

    # --- LaTeX bodies ---
    print("\n" + "=" * 78)
    print("LaTeX body, Exhibit 1 (AY & Latest & Ult R & Ult ours & diff & IBNR R & IBNR ours & diff & SE R & SE ours & diff)")
    print("=" * 78)
    for r in rows:
        print(f"{r['origin']} & {fmt(r['latest'])} & {fmt(r['ult_R'])} & {fmt(r['ult'], 1)} & {r['ult']-r['ult_R']:+.2f} & {fmt(r['ibnr_R'])} & {fmt(r['ibnr'], 1)} & {r['ibnr']-r['ibnr_R']:+.2f} & {fmt(r['se_R'])} & {fmt(r['se'], 1)} & {r['se']-r['se_R']:+.2f} \\\\")
    print(f"Total & {fmt(sum(latest))} & {fmt(T['Ultimate'], 2)} & {fmt(tu, 2)} & {tu-T['Ultimate']:+.2f} & {fmt(T['IBNR'], 2)} & {fmt(tr, 2)} & {tr-T['IBNR']:+.2f} & {fmt(T['Mack.S.E'], 2)} & {fmt(ts, 2)} & {ts-T['Mack.S.E']:+.2f} \\\\")
    print("\n" + "=" * 78)
    print("LaTeX body, Exhibit 2 (AY & IBNR & Mack est. s.e. & resampling est. s.e. & diff of squares & rel. diff & share of MSEP)")
    print("=" * 78)
    for r in ex2:
        print(f"{r['origin']} & {fmt(r['ibnr'])} & {fmt(math.sqrt(r['mack_term']), 1)} & {fmt(math.sqrt(r['resampling_term']), 1)} & {fmt(r['diff'], 1)} & {100*r['rel']:.3f}\\% & {100*r['share_of_msep']:.3f}\\% \\\\")
    print(f"Sum of single-year terms & {fmt(tr)} & {fmt(math.sqrt(tot_m), 1)} & {fmt(math.sqrt(tot_b), 1)} & {fmt(tot_b-tot_m, 1)} & {100*(tot_b-tot_m)/tot_m:.3f}\\% & \\\\")
    print(f"Total incl. cross terms & {fmt(tr)} & {fmt(math.sqrt(tot_est_mack), 1)} & {fmt(math.sqrt(tot_est_bbmw), 1)} & {fmt(tot_est_bbmw-tot_est_mack, 1)} & {100*(tot_est_bbmw-tot_est_mack)/tot_est_mack:.3f}\\% & {100*(tot_est_bbmw-tot_est_mack)/total:.3f}\\% \\\\")

    print("\nRESULT:", "our calculation reproduces R ChainLadder (est.sigma='Mack') to printed precision" if match_mack else "MISMATCH against R (see Exhibit 1)")

    if "--json" in sys.argv:
        out = dict(f=f, S=S, sigma2_mack_rule=sig2, sigma2_loglinear=sig2_ll, loglinear_pvalue=pval,
                   exhibit1=rows, exhibit1_totals=dict(ult=tu, ibnr=tr, se=ts, published=T),
                   loglinear_se=ll_rows, total_se_loglinear=math.sqrt(total_ll),
                   exhibit2=ex2, exhibit2_sum=dict(mack=tot_m, resampling=tot_b),
                   total=dict(process=proc_total, est_mack=tot_est_mack, est_resampling=tot_est_bbmw, msep_mack=total),
                   matches_R_under_mack_rule=match_mack)
        json.dump(out, open(os.path.join(HERE, "raa_case_study_results.json"), "w"), indent=1)
        print("wrote raa_case_study_results.json")
    return 0 if match_mack else 1


if __name__ == "__main__":
    sys.exit(main())
