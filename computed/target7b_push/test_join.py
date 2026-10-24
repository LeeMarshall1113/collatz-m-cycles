"""Validation of b3join.
  python test_join.py set t N...      set of valid sigma (k0+l0<N) with value >= N+t: join vs
                                       exhaustive enumeration of all four parameters (O(N^4))
  python test_join.py brute N1 N2     B3 from join (t = 0) vs brute force and b3.slow
  python test_join.py grid FILE...    B3 from join vs the exact grid values in json files
"""
import sys, os, json, math, time
import b3join as J
import b3 as B3M
sys.path.insert(0, J.T7)
import brute as BR   # noqa: E402


def exhaustive_set(N, t, Kmax):
    U, c = J.pack_rows(N, Kmax)
    S = set()
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            for K in range(k0 + 1, Kmax + 1):
                for l1 in range(1, N + math.ceil(0.585 * K) + 2):
                    r = J.exact_value(c, k0, l0, K, l1)
                    if r and r[0] >= N + t:
                        S.add(r)
    return S


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'set':
        t = int(a[1])
        for N in map(int, a[2:]):
            Kmax = J.b2_of(N)
            r = J.b3_join(N, t, Kmax=Kmax, verbose=False)
            fs = set(r['found'])
            ex = exhaustive_set(N, t, Kmax)
            print(f"N={N} t={t} join={len(fs)} exhaustive={len(ex)} IDENTICAL={fs == ex}", flush=True)
    elif a[0] == 'brute':
        for N in range(int(a[1]), int(a[2]) + 1):
            r = J.b3_exact(N, t=0)
            bs = B3M.slow(N)[0]
            br = None
            if N <= 22:
                br = int(BR.runs(N, 3).max())
            print(f"N={N} join={r['B3']} slow={bs} brute={br} OK={r['B3'] == bs and (br is None or br == bs)}",
                  flush=True)
    elif a[0] == 'grid':
        ref = {}
        for f in a[1:]:
            for k, v in json.load(open(f)).items():
                ref[int(k)] = v['B3'] if isinstance(v, dict) else v
        bad = 0
        for N in sorted(ref):
            t0 = time.time()
            r = J.b3_exact(N)
            ok = r['B3'] == ref[N]
            bad += not ok
            print(f"N={N} join={r['B3']} ref={ref[N]} {'OK' if ok else 'MISMATCH'} t={r['t']} "
                  f"cand={r['ncand']} {time.time() - t0:.1f}s ks={r['witness_ks']}", flush=True)
        print("mismatches", bad)
