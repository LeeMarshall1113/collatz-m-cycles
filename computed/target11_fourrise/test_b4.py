"""B4 join vs literal brute force over all odd n < 2^N: (a) B4 equal, (b) the set of n with value >= N+t
found by the join contains every such n (t = several thresholds)."""
import sys, time
import b4join as J
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else None
if CAP: J.PAGE = 3


def brute(N):
    vals = {}
    for n in range(1, 1 << N, 2):
        vals[n] = J.runs_value(n)
    return vals


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    t0 = time.time()
    V = brute(N)
    b = max(V.values())
    res = []
    for t in sorted({b - N - 2, b - N - 4, b - N - 6}):
        best, wit, ok, fs = J.B4(N, t, want_set=True, cap=CAP)
        truth = {n for n, v in V.items() if v >= N + t}
        res.append((t, ok and best == b, truth <= fs, len(truth)))
    print(f"N={N} brute B4={b} (N+{b - N})  per t (t, best==brute, all found, #truth): {res}  {time.time() - t0:.1f}s", flush=True)
    assert all(r[1] and r[2] for r in res)
print("ALL OK")
