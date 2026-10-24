"""Independent exact B2(N), B3(N) by a mixed 3-adic / 2-adic decomposition (target 7c referee).

B_r(N) = max over odd n < 2^N of the total length of the first r ascending runs (T(n) = (3n+1)/2
for odd n, n/2 for even n).

Different from the repo's methods (which work with the 2-adic nu(sigma) and z_N): here the first
block is solved in the integers.  For odd n < 2^N with first block (k0, l0):
    n + 1 = 2^k0 a,  a odd,  a <= A := 2^(N-k0),   3^k0 a - 1 = 2^l0 n1,  n1 odd.
Conversely, for any odd n1 >= 1 with 2^l0 n1 + 1 == 0 (mod 3^k0), a := (2^l0 n1 + 1)/3^k0 is
automatically odd, and n := 2^k0 a - 1 has first block exactly (k0, l0) (n1 odd).  So, with
r := the residue of n1 mod 3^k0 (r = -2^-l0 mod 3^k0) and n1 = r + 3^k0 t (t >= 0),
    n < 2^N  <=>  a <= A  <=>  n1 <= X := floor((3^k0 A - 1)/2^l0)  <=>  t <= T := floor((X-r)/3^k0).
The remaining runs of n1 are fixed by n1 mod 2^L: "the next runs are (k1, l1) and k2 >= j"
<=> n1 == nu1 (mod 2^L), L = k1+l1+j, nu1 = -1 + u_k1 (1 - 2^l1) (u_k = (2/3)^k in Z_2), and
"k1 >= j" <=> n1 == -1 (mod 2^j).  In terms of t:  t == tau (mod 2^L), tau = (nu1 - r) 3^-k0
in Z_2, and some t in [0, T] exists iff (tau mod 2^L) <= T.  L -> (tau mod 2^L) is
nondecreasing, so the largest feasible L is
    b - 1                         if (tau mod 2^b) > T,  b = bitlength(T)
    (least set bit of tau >= b)   otherwise.
Everything is exact integer arithmetic mod 2^W with W = N + 2*N + 64 bits of precision
(more than any L that can occur: L <= log2 of n1's size + 1 < 2N + 2).
"""
import sys, time
import gmpy2
from gmpy2 import mpz


def maxL(tau, T, W):
    """largest L >= 0 with (tau mod 2^L) <= T, given tau mod 2^W (assert the answer < W)"""
    if T < 0:
        return -1
    b = int(T).bit_length() if T > 0 else 0
    if b == 0:
        # T == 0: need tau mod 2^L == 0
        L = gmpy2.bit_scan1(tau) if tau else W
        assert L < W
        return L
    if (tau & ((1 << b) - 1)) > T:
        return b - 1
    hi = tau >> b
    assert hi != 0, "precision"
    return b + gmpy2.bit_scan1(hi)


def B2(N, want=None):
    W = 3 * N + 64
    MOD = mpz(1) << W
    best, wit = -1, None
    for k0 in range(1, N + 1):
        A = mpz(1) << (N - k0)
        p3 = mpz(3) ** k0
        inv3 = gmpy2.invert(p3, MOD)
        top = p3 * A - 1
        l0 = 1
        while True:
            X = top >> l0
            if X < 1:
                break
            r = (-gmpy2.invert(mpz(2) ** l0 % p3, p3)) % p3 if k0 > 0 else 0
            if r % 1 == 0 and r <= X:
                T = (X - r) // p3
                tau = ((-1 - r) * inv3) % MOD
                L = maxL(tau, T, W)          # k1 = largest j with n1 == -1 mod 2^j for some t
                if L >= 1:
                    v = k0 + L
                    if v > best:
                        best, wit = v, (k0, l0, L)
            l0 += 1
    return best, wit


def B3(N, target=None):
    """exact B3(N).  If target is given, only sigma that can reach value >= target are fully
    evaluated (pruning by the exact upper bound value <= k0 + k1 + maxk2 is not used; every sigma
    is evaluated), and the run returns (best, witness, count_of_sigma_with_value>=target)."""
    W = 3 * N + 64
    MOD = mpz(1) << W
    best, wit, cnt = -1, None, 0
    # u_k mod 2^W for k up to 2N+2
    inv3 = gmpy2.invert(mpz(3), MOD)
    u = [mpz(1)]
    for k in range(1, 2 * N + 70):
        u.append((u[-1] * 2 * inv3) % MOD)
    for k0 in range(1, N + 1):
        A = mpz(1) << (N - k0)
        p3 = mpz(3) ** k0
        inv3k = gmpy2.invert(p3, MOD)
        top = p3 * A - 1
        l0 = 1
        while True:
            X = top >> l0
            if X < 1:
                break
            r = (-gmpy2.invert((mpz(2) ** l0) % p3, p3)) % p3
            if r <= X:
                T = (X - r) // p3
                k1 = 1
                while (mpz(1) << k1) <= X + 1:     # n1 + 1 >= 2^k1
                    # n1 + 1 = 2^k1 b1 with b1 <= (X+1)/2^k1; n2 = (3^k1 b1 - 1)/2^l1 >= 1
                    bmax = (X + 1) >> k1
                    lim = mpz(3) ** k1 * bmax
                    uk = u[k1]
                    l1 = 1
                    while (mpz(1) << l1) <= lim:
                        nu1 = (-1 + uk * (1 - (mpz(1) << l1))) % MOD
                        tau = ((nu1 - r) * inv3k) % MOD
                        L = maxL(tau, T, W)
                        k2 = L - k1 - l1
                        if k2 >= 1:
                            v = k0 + k1 + k2
                            if target is not None and v >= target:
                                cnt += 1
                            if v > best:
                                best, wit = v, (k0, l0, k1, l1, k2)
                        l1 += 1
                    k1 += 1
            l0 += 1
    return best, wit, cnt


def T(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def runs(n, r):
    ks = []
    for _ in range(r):
        k = 0
        while n & 1:
            n = T(n); k += 1
        ks.append(k)
        while not n & 1:
            n = T(n)
    return ks


def witness(N, k0, l0, k1, l1, k2):
    """rebuild an n < 2^N with these runs (k2 >= given) by CRT, and simulate it literally"""
    W = 3 * N + 64
    MOD = 1 << W
    p3 = 3 ** k0
    r = (-pow(2 ** l0, -1, p3)) % p3
    X = (p3 * 2 ** (N - k0) - 1) >> l0
    Tm = (X - r) // p3
    u = 1
    for _ in range(k1):
        u = (u * 2 * pow(3, -1, MOD)) % MOD
    nu1 = (-1 + u * (1 - 2 ** l1)) % MOD
    L = k1 + l1 + k2
    tau = ((nu1 - r) * pow(p3, -1, MOD)) % MOD
    t = tau % (1 << L)
    assert t <= Tm
    n1 = r + p3 * t
    a = (2 ** l0 * n1 + 1) // p3
    n = 2 ** k0 * a - 1
    assert n < 2 ** N and n & 1
    return n, runs(n, 3)


def brute(N):
    b2 = b3 = 0
    for n in range(1, 2 ** N, 2):
        k = runs(n, 3)
        b2 = max(b2, k[0] + k[1]); b3 = max(b3, sum(k))
    return b2, b3


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'brute':
        for N in range(int(a[1]), int(a[2]) + 1):
            t = time.time()
            bb2, bb3 = brute(N)
            c2 = B2(N)[0]; c3 = B3(N)[0]
            print(N, 'brute', bb2, bb3, 'crt', c2, c3, 'OK' if (bb2, bb3) == (c2, c3) else 'MISMATCH', flush=True)
    else:
        for N in map(int, a[1:]):
            t = time.time()
            if a[0] == 'b3':
                v, w, _ = B3(N)
                n, ks = witness(N, *w)
                print(f"B3({N}) = {v}  sigma+k2={w}  witness n={n} runs={ks} sum={sum(ks)}  {time.time()-t:.0f}s", flush=True)
                assert sum(ks) == v
            else:
                v, w = B2(N)
                print(f"B2({N}) = {v}  (k0,l0,k1)={w}  {time.time()-t:.1f}s", flush=True)
