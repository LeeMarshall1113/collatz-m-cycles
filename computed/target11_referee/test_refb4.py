"""validate refb4 vs literal brute force: exact B4 and complete near-maximiser sets, N = 4..22"""
import sys, time
import refb4 as B
lo, hi = int(sys.argv[1]), int(sys.argv[2])
# parity-vector sanity of nu (Theorem R, r = 4) on a few sigma
def Tm(x): return (3 * x + 1) // 2 if x & 1 else x // 2
L = 400; mod = 1 << L; i3 = pow(3, -1, mod)
u = lambda b: pow(2 * i3 % mod, b, mod)
import random
rnd = random.Random(1)
for _ in range(200):
    k0, l0, k1, l1, k2, l2 = (rnd.randint(1, 12) for _ in range(6))
    K1, K2, h = k0 + k1, k0 + k1 + k2, l0 + l1
    nu = (-1 + u(k0) - (u(k0) << l0) + (u(K1) << l0) - (u(K1) << h) + (u(K2) << h) - (u(K2) << (h + l2))) % mod
    w = '1' * k0 + '0' * l0 + '1' * k1 + '0' * l1 + '1' * k2 + '0' * l2 + '1' * 40
    x, got = nu, ''
    for _ in range(len(w)):
        got += str(x & 1); x = Tm(x)
    assert got == w, (k0, l0, k1, l1, k2, l2)
print("parity vector of nu: 200 random sigma OK")
allok = True
for N in range(lo, hi + 1):
    vals = {n: B.value4(n) for n in range(1, 1 << N, 2)}
    b4 = max(vals.values())
    ok = True
    for V in (b4 + 1, b4, b4 - 1, b4 - 2):
        f, st = B.search(N, V, verbose=False)
        want = {n for n, v in vals.items() if v >= V}
        ok &= set(f) == want and all(vals[n] == v for n, v in f.items())
    allok &= ok
    print(f"N={N} brute B4={b4}  refb4 sets for V=B4+1..B4-2 identical: {ok}", flush=True)
print("ALL OK" if allok else "MISMATCH")
