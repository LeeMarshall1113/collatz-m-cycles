"""Referee (target 11), checks 2 and 4 at m: own survivor count + own screen of every survivor.

(A) Completeness of the candidate list (fastchain.candidates = fastshapes lattice points).
    Own pieces: N(K) = min(400, floor(m2 K/(m G(m2)))), M(K) likewise, are step functions of K; between
    consecutive steps lam(K) = min(m/X0, min_m2 (m-m2)/X0 + 1/(2^N-1) + (m2-1)/(2^M-1)) is constant (exact
    Fractions).  A shape survives iff 0 < p - K delta < lam/ln2 (p = floor(K delta) + 1).  The number of
    survivors per piece is counted exactly with a floor-sum (Euclid) over K, at 2^-320 rational brackets
    of delta and lam/ln2 (both brackets must agree).  Then the candidates are tested against the same
    condition (e = p - K delta to 2^-320) and counted per piece: equal counts in every piece  <=>  the
    candidate list contains every survivor (candidates are distinct lattice points).
(B) Own screen of every survivor: Ub from ALL m2 (floats, then inflated 1e-9; N, M deflated so they
    stay <= the exact floors), Y0 rounded up to 2^-8, own chain (refchain) per bucket with grids
    {B2,B3} and {B2,B3,B4}; bound < 1 (exact integer comparison) closes the shape.
usage: python refshapes.py m
"""
import sys, os, math, time, json, bisect, pickle
from fractions import Fraction as Fr
import numpy as np
import mpmath
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refchain as RC                     # noqa: E402

mpmath.mp.prec = 1200
QB = 320
Q = 1 << QB
DQ = mpmath.log(3, 2) * Q
D_A_LO, D_A_HI = int(mpmath.floor(DQ)) - 1, int(mpmath.floor(DQ)) + 2      # delta in (D_A_LO/Q, D_A_HI/Q)
LN2 = mpmath.log(2)
X0 = RC.X0
NCAP = 400


def floor_sum(n, m, a, b):
    """sum_{i<n} floor((a i + b)/m), a, b >= 0"""
    ans = 0
    while True:
        if a >= m:
            ans += (n - 1) * n // 2 * (a // m); a %= m
        if b >= m:
            ans += n * (b // m); b %= m
        y = a * n + b
        if y < m:
            return ans
        n, b = y // m, y % m
        m, a = a, m


def count_piece(Ka, Kb, E):
    """# K in [Ka, Kb) with floor(K d + E/Q) > floor(K d), for d = both delta brackets"""
    n = Kb - Ka
    r = []
    for A in (D_A_LO, D_A_HI):
        r.append(floor_sum(n, Q, A, A * Ka + E) - floor_sum(n, Q, A, A * Ka))
    return r


def pieces(m, Kceil):
    G = [RC.Gsum(j) for j in range(m + 1)]
    ev = []
    for m2 in range(1, m + 1):
        for kind, g in ((0, m * G[m2] / m2), (1, m * (1 + G[m2 - 1]) / m2)):
            for j in range(1, NCAP + 1):
                K = RC.ceilfr(j * g)            # N(K) >= j  <=>  K >= j g
                if K >= Kceil:
                    break
                ev.append((K, m2, kind))
    ev.sort()
    N = [0] * (m + 1); M = [0] * (m + 1)
    b = [None] * (m + 1)
    out = []
    Ka, i = 1, 0
    base = Fr(m, X0)

    def cur():
        v = base
        for m2 in range(1, m + 1):
            if b[m2] is not None and b[m2] < v:
                v = b[m2]
        return v
    lam = base
    while i <= len(ev):
        K = ev[i][0] if i < len(ev) else Kceil
        if K > Ka:
            out.append((Ka, K, lam))
            Ka = K
        if i == len(ev):
            break
        while i < len(ev) and ev[i][0] == K:
            _, m2, kind = ev[i]
            if kind == 0:
                N[m2] += 1
            else:
                M[m2] += 1
            if N[m2] >= 1 and M[m2] >= 1:
                b[m2] = Fr(m - m2, X0) + Fr(1, 2 ** N[m2] - 1) + Fr(m2 - 1, 2 ** M[m2] - 1)
            i += 1
        lam = cur()
    return out


def eta_brackets(lam):
    v = mpmath.mpf(lam.numerator) / lam.denominator / LN2 * Q
    return int(mpmath.floor(v)) - 1, int(mpmath.floor(v)) + 2


def main(m):
    sys.path.insert(0, os.path.join(HERE, '..', 'target11_fourrise'))
    import fastchain as FC
    t0 = time.time()
    Kceil, cand = FC.candidates(m)
    print(f"m={m}: fastchain candidates {len(cand)} Kceil={Kceil} ({time.time() - t0:.0f}s)", flush=True)
    # Kceil: own check of the Rhin/Thm-21(m2=m) exclusion g(K) >= 0 at Kceil, and g increasing beyond
    Gm = RC.Gsum(m)
    mpmath.mp.prec = 300
    gK = lambda K: (mpmath.mpf(K) * Gm.denominator / Gm.numerator - 2) * mpmath.log(2) - mpmath.log(m) \
        - mpmath.mpf('13.3') * (mpmath.mpf('0.46057') + mpmath.log(K))
    print(f"  own Rhin check: g(Kceil) = {mpmath.nstr(gK(Kceil), 8)} (>=0 needed), g(Kceil-1) = {mpmath.nstr(gK(Kceil - 1), 8)}, "
          f"monotone beyond {float(13.3 * Gm / Fr(693, 1000)):.3e} < Kceil: {13.3 * Gm / Fr(693, 1000) < Kceil}", flush=True)
    mpmath.mp.prec = 1200
    t1 = time.time()
    pcs = pieces(m, Kceil)
    starts = [a for a, _, _ in pcs]
    Es = [eta_brackets(l) for _, _, l in pcs]
    cnt_exact = []
    bad = 0
    for (Ka, Kb, l), (Elo, Ehi) in zip(pcs, Es):
        c1 = count_piece(Ka, Kb, Elo); c2 = count_piece(Ka, Kb, Ehi)
        if len(set(c1 + c2)) != 1:
            bad += 1
        cnt_exact.append(c2[1])
    tot = sum(cnt_exact)
    print(f"  own pieces {len(pcs)}; exact survivor count (floor-sum) = {tot}; ambiguous pieces {bad} ({time.time() - t1:.0f}s)", flush=True)
    # candidates per piece
    t2 = time.time()
    cnt_c = [0] * len(pcs)
    surv = []
    amb = 0
    for K, p in cand:
        i = bisect.bisect_right(starts, K) - 1
        elo = p * Q - K * D_A_HI           # (p - K delta) Q > elo
        ehi = p * Q - K * D_A_LO
        Elo, Ehi = Es[i]
        if elo > 0 and ehi < Elo:
            cnt_c[i] += 1
            surv.append((K, p, elo))
        elif not (ehi <= 0 or elo >= Ehi):
            amb += 1
    mism = [(pcs[i][0], cnt_exact[i], cnt_c[i]) for i in range(len(pcs)) if cnt_exact[i] != cnt_c[i]]
    print(f"  candidates that survive (own test) {len(surv)}; ambiguous {amb}; pieces with count mismatch "
          f"{len(mism)} {mism[:5]}  -> candidate list {'CONTAINS all survivors' if not mism and not amb and not bad else 'NOT PROVEN'} "
          f"({time.time() - t2:.0f}s)", flush=True)
    del cand
    # (B) own screen of every survivor
    t3 = time.time()
    snap = os.path.join(HERE, '..', 'target11_fourrise', 'b4_grid_snapshot_le852.json')
    tabs4 = RC.load_grids(snap)
    tabs3 = {2: tabs4[2], 3: tabs4[3]}
    n = len(surv)
    Kf = np.array([float(K) for K, _, _ in surv])
    lo = np.array([float(Fr(e, Q)) for _, _, e in surv]) * float(RC.L2_LO) * (1 - 1e-12)   # <= (p - K delta) ln2
    G = [RC.Gsum(j) for j in range(m + 1)]
    best = np.full(n, np.inf)
    for m2 in range(1, m):                    # m2 = m: (m - m2) = 0 would give Ub = 0; ignoring it is conservative
        gN = float(m * G[m2] / m2); gM = float(m * (1 + G[m2 - 1]) / m2)
        Nn = np.minimum(np.floor(Kf / gN * (1 - 1e-12)), NCAP)
        Mm = np.minimum(np.floor(Kf / gM * (1 - 1e-12)), NCAP)
        with np.errstate(over='ignore', divide='ignore', invalid='ignore'):
            tail = (1.0 / (2.0 ** Nn - 1) + (m2 - 1) / (2.0 ** Mm - 1)) * (1 + 1e-12)
            room = lo - tail
            ub = np.where((Nn >= 1) & (Mm >= 1) & (room > lo * 1e-6), (m - m2) / room * (1 + 1e-9), np.inf)
        best = np.minimum(best, ub)
    small = best <= float(X0) * (1 - 1e-9)
    noub = ~np.isfinite(best)
    with np.errstate(divide='ignore'):
        bk = np.ceil((np.log2(best) + 1e-6) * 256)
    cache3, cache4 = {}, {}

    def S(b, tabs, cache):
        if b not in cache:
            Y, _ = RC.chain(m, int(b) << 56, tabs)
            cache[b] = sum(Y)
        return cache[b]
    res = []
    open3, open4 = [], []
    for i in range(n):
        if small[i] or noub[i]:
            if noub[i]:
                open3.append(i); open4.append(i)
            continue
        K = surv[i][0]
        s3 = S(bk[i], tabs3, cache3)
        s4 = S(bk[i], tabs4, cache4)
        r3, r4 = s3 / (K * RC.ONE), s4 / (K * RC.ONE)
        if s3 >= K * RC.ONE:
            open3.append(i)
        if s4 >= K * RC.ONE:
            open4.append(i)
        res.append((r4, r3, i))
    res.sort(reverse=True)
    print(f"  own screen of {n} survivors ({time.time() - t3:.0f}s): small(Ub<=X0) {int(small.sum())}, no-Ub {int(noub.sum())}, "
          f"buckets {len(cache4)}; NOT closed by screen: with B4 {len(open4)}, B2+B3 only {len(open3)}", flush=True)
    for r4, r3, i in res[:8]:
        print(f"    screen bound {r4:.6f} (B2B3 only {r3:.6f})  K={surv[i][0]}", flush=True)
    # exact own chain for every shape the screen left open, and the top 50 by screen bound
    todo = sorted(set(open4) | set(open3) | {i for _, _, i in res[:50]})
    rows = []
    for i in todo:
        K, p, _ = surv[i]
        r4, tr4 = RC.ratio(m, K, p, tabs4)
        r3, _ = RC.ratio(m, K, p, tabs3)
        used4 = sorted({pt for t, how, pt, c, b in tr4 if how == 4}) if tr4 else []
        rows.append((K, p, float(r4) if r4 is not None else None, float(r3) if r3 is not None else None, used4))
        print(f"    exact own chain K={K}: ratio B2B3B4 {float(r4):.7f}  B2B3 {float(r3):.7f}  binding B4 pts {used4}", flush=True)
    nf = sum(1 for r in rows if r[2] is None or r[2] >= 1)
    print(f"m={m}: own result: survivors {n}, failures with B4 grid {nf + sum(1 for i in open4 if i not in todo)}; "
          f"shapes needing B4 (B2B3 ratio >= 1): {[r[0] for r in rows if r[3] is None or r[3] >= 1]}", flush=True)
    pickle.dump(dict(rows=rows, top=[(r4, r3, surv[i][0], surv[i][1]) for r4, r3, i in res[:2000]]),
                open(os.path.join(HERE, f'refshapes_{m}.pkl'), 'wb'))




def main_stream(m, CH=200000):
    """same checks as main(), but candidates are generated interval by interval (fastchain.candidates'
    exact recipe: fastshapes.merge(intervals), box_points with eta = L/L2LO (1 + 1e-9), 1 <= K < Kceil) and
    processed in chunks, so memory stays small."""
    sys.path.insert(0, os.path.join(HERE, '..', 'target11_fourrise'))
    import fastchain as FC
    fs = FC.fs
    t0 = time.time()
    Kceil = fs.shapes.rhin_ceiling(m)
    iv = fs.merge(fs.intervals(m, Kceil))
    Gm = RC.Gsum(m)
    mpmath.mp.prec = 300
    gK = lambda K: (mpmath.mpf(K) * Gm.denominator / Gm.numerator - 2) * mpmath.log(2) - mpmath.log(m) \
        - mpmath.mpf('13.3') * (mpmath.mpf('0.46057') + mpmath.log(K))
    print(f"m={m}: Kceil={Kceil}; own Rhin check: g(Kceil) = {mpmath.nstr(gK(Kceil), 8)} (>=0 needed), "
          f"g(Kceil-1) = {mpmath.nstr(gK(Kceil - 1), 8)}, monotone beyond {float(13.3 * Gm / Fr(693, 1000)):.3e} < Kceil: "
          f"{13.3 * Gm / Fr(693, 1000) < Kceil}; {len(iv)} merged intervals", flush=True)
    mpmath.mp.prec = 1200
    t1 = time.time()
    pcs = pieces(m, Kceil)
    starts = [a for a, _, _ in pcs]
    Es = [eta_brackets(l) for _, _, l in pcs]
    cnt_exact, bad = [], 0
    for (Ka, Kb, l), (Elo, Ehi) in zip(pcs, Es):
        c1 = count_piece(Ka, Kb, Elo); c2 = count_piece(Ka, Kb, Ehi)
        if len(set(c1 + c2)) != 1:
            bad += 1
        cnt_exact.append(c2[1])
    print(f"  own pieces {len(pcs)}; exact survivor count (floor-sum) = {sum(cnt_exact)}; ambiguous pieces {bad} "
          f"({time.time() - t1:.0f}s)", flush=True)
    snap = os.path.join(HERE, '..', 'target11_fourrise', 'b4_grid_snapshot_le852.json')
    tabs4 = RC.load_grids(snap)
    tabs3 = {2: tabs4[2], 3: tabs4[3]}
    G = [RC.Gsum(j) for j in range(m + 1)]
    gNs = [float(m * G[m2] / m2) if m2 else 1.0 for m2 in range(m)]
    gMs = [float(m * (1 + G[m2 - 1]) / m2) if m2 else 1.0 for m2 in range(m)]
    cache3, cache4 = {}, {}

    def S(b, tabs, cache):
        if b not in cache:
            Y, _ = RC.chain(m, int(b) << 56, tabs)
            cache[b] = sum(Y)
        return cache[b]
    cnt_c = [0] * len(pcs)
    st = dict(cand=0, surv=0, amb=0, small=0, noub=0)
    open3, open4, top = [], [], []
    l2lo = float(RC.L2_LO)

    def process(buf):
        surv = []
        for K, p in buf:
            i = bisect.bisect_right(starts, K) - 1
            elo = p * Q - K * D_A_HI
            ehi = p * Q - K * D_A_LO
            Elo, Ehi = Es[i]
            if elo > 0 and ehi < Elo:
                cnt_c[i] += 1
                surv.append((K, p, elo))
            elif not (ehi <= 0 or elo >= Ehi):
                st['amb'] += 1
        n = len(surv)
        st['surv'] += n
        if not n:
            return
        Kf = np.array([float(K) for K, _, _ in surv])
        lo = np.array([float(Fr(e, Q)) for _, _, e in surv]) * l2lo * (1 - 1e-12)
        best = np.full(n, np.inf)
        for m2 in range(1, m):
            Nn = np.minimum(np.floor(Kf / gNs[m2] * (1 - 1e-12)), NCAP)
            Mm = np.minimum(np.floor(Kf / gMs[m2] * (1 - 1e-12)), NCAP)
            with np.errstate(over='ignore', divide='ignore', invalid='ignore'):
                tail = (1.0 / (2.0 ** Nn - 1) + (m2 - 1) / (2.0 ** Mm - 1)) * (1 + 1e-12)
                room = lo - tail
                ub = np.where((Nn >= 1) & (Mm >= 1) & (room > 0), (m - m2) / room * (1 + 1e-9), np.inf)
            best = np.minimum(best, ub)
        small = best <= float(X0) * (1 - 1e-9)
        noub = ~np.isfinite(best)
        with np.errstate(divide='ignore', invalid='ignore'):
            bk = np.ceil((np.log2(best) + 1e-6) * 256)
        st['small'] += int(small.sum()); st['noub'] += int(noub.sum())
        for i in range(n):
            K, p, _ = surv[i]
            if noub[i]:
                open3.append((K, p)); open4.append((K, p)); continue
            if small[i]:
                continue
            s3 = S(bk[i], tabs3, cache3); s4 = S(bk[i], tabs4, cache4)
            if s3 >= K * RC.ONE:
                open3.append((K, p))
            if s4 >= K * RC.ONE:
                open4.append((K, p))
            top.append((s4 / (K * RC.ONE), s3 / (K * RC.ONE), K, p))
        top.sort(reverse=True)
        del top[60:]
    buf = []
    for Ka, Kb, L in iv:
        eta = Fr(L) / FC.C.L2LO * (1 + Fr(1, 10 ** 9))
        pts = set(p for p in fs.box_points(Ka, Kb, eta)[0] if 1 <= p[0] < Kceil)
        st['cand'] += len(pts)
        buf.extend(pts)
        if len(buf) >= CH:
            process(buf); buf = []
    process(buf)
    mism = [(pcs[i][0], cnt_exact[i], cnt_c[i]) for i in range(len(pcs)) if cnt_exact[i] != cnt_c[i]]
    print(f"  candidates {st['cand']} (fastchain reported 5291301 at m=127); surviving (own exact test) {st['surv']}; "
          f"ambiguous {st['amb']}; pieces with count mismatch {len(mism)} {mism[:5]} -> candidate list "
          f"{'CONTAINS all survivors' if not mism and not st['amb'] and not bad else 'NOT PROVEN'}", flush=True)
    print(f"  own screen ({time.time() - t0:.0f}s total): small(Ub<=X0) {st['small']}, no-Ub {st['noub']}, buckets {len(cache4)}; "
          f"NOT closed by screen: with B4 {len(open4)}, B2+B3 only {len(open3)}", flush=True)
    for r4, r3, K, p in top[:8]:
        print(f"    screen bound {r4:.6f} (B2B3 only {r3:.6f})  K={K}", flush=True)
    todo = sorted(set(open4) | set(open3) | {(K, p) for _, _, K, p in top[:50]})
    rows = []
    for K, p in todo:
        r4, tr4 = RC.ratio(m, K, p, tabs4)
        r3, _ = RC.ratio(m, K, p, tabs3)
        used4 = sorted({pt for t, how, pt, c, b in tr4 if how == 4}) if tr4 else []
        rows.append((K, p, r4, r3, used4))
        print(f"    exact own chain K={K}: ratio B2B3B4 {float(r4):.7f}  B2B3 {float(r3):.7f}  binding B4 pts {used4}", flush=True)
    nf = sum(1 for r in rows if r[2] is None or r[2] >= 1)
    print(f"m={m}: own result: survivors {st['surv']}, failures with B4 grid {nf}; shapes needing B4 (B2B3 ratio >= 1): "
          f"{[r[0] for r in rows if r[3] is None or r[3] >= 1]}", flush=True)
    pickle.dump(dict(rows=rows, top=top), open(os.path.join(HERE, f'refshapes_{m}.pkl'), 'wb'))


if __name__ == "__main__":
    for m in map(int, sys.argv[1:]):
        main_stream(m)
