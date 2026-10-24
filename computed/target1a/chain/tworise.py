"""Two-rise bound B(N): for every odd n < 2^N, k0 + k1 <= B, where k0 is the first rise of n
(n + 1 = a 2^k0, a odd), l >= 1 the following descent and k1 the next rise.  Own implementation.

Derivation.  T^k0 n = 3^k0 a - 1 = 2^l n', n' odd, n' + 1 = a' 2^k1.  Hence
3^k0 a + 2^l - 1 = 2^(l+k1) a', i.e.  a == gamma := (1 - 2^l) 3^(-k0)  (mod 2^(l+k1)).
n < 2^N gives a < 2^A, A = N - k0 (A = 1 if k0 = N, then a = 1).  So gamma mod 2^(l+k1) < 2^A:
bits A .. l+k1-1 of gamma vanish, i.e. l + k1 <= z(k0,l) := lowest set bit of gamma at index >= A.
So k0 + k1 <= k0 - l + z(k0, l)  and  B(N) = max over k0 in [1,N], l >= 1 of that.
  * l > z_A(c) (c = 3^-k0): gamma == c mod 2^l has bit z_A(c) in [A, l) set -> no configuration.
  * A <= l <= z_A(c), and l <= LDIR: exact z (direct).
  * LDIR < l < A: if bits [A, A+E) of gamma are not all 0 then z < A + E and the value is
    < k0 - l + A + E <= N + E - LDIR - 1 (so <= N + E - LDIR - 2).  Bits [A, A+E) of
    gamma = c - c 2^l are (P - W_l - borrow) mod 2^E with P = bits [A, A+E) of c, W_l = bits
    [A-l, A-l+E) of c, borrow in {0,1}; so they vanish only if W_l in {P, P-1 mod 2^E}.  All such
    positions are found by substring search in the LSB-first bit string of c, and get the exact z.
Output: max(N, N + E - LDIR - 2, all exact values).  (k1 >= 1 so the true max is >= k0 + 1;
taking the max with N is harmless: B only needs to be an upper bound.)
Precision: c is kept mod 2^W; every exact z found must be < W (asserted).
"""
import sys, time


def zA(g, A, W):
    h = g >> A
    assert h != 0, "W too small"
    z = A + ((h & -h).bit_length() - 1)
    assert z < W
    return z


def bound(N, E=24, LDIR=16, exact=False, W=None):
    """B(N) as above; exact=True does every l directly (slow, for validation)"""
    if W is None:
        W = 2 * N + 4 * E + 256
    mod = 1 << W
    mask = mod - 1
    i3 = pow(3, -1, mod)
    c = 1
    best = max(N, N + E - LDIR - 2) if not exact else N
    arg = None
    nhits = 0
    for k0 in range(1, N + 1):
        c = (c * i3) & mask
        A = N - k0 if k0 < N else 1
        zc = zA(c, A, W)

        def val(l):
            g = (c - (c << l)) & mask
            return k0 - l + zA(g, A, W)
        ls = set(range(A, zc + 1))
        if exact:
            ls.update(range(1, A))
        else:
            ls.update(range(1, min(A, LDIR + 1)))
            if A - 1 > LDIR:
                # bit string of c, LSB first, positions 0 .. A+E-1
                s = format(c & ((1 << (A + E)) - 1), 'b').zfill(A + E)[::-1]
                P = (c >> A) & ((1 << E) - 1)
                pats = {format(P, 'b').zfill(E)[::-1], format((P - 1) % (1 << E), 'b').zfill(E)[::-1]}
                for pat in pats:
                    j = s.find(pat, 1)
                    while j != -1:
                        l = A - j            # window at position i = A - l
                        if LDIR < l < A:
                            ls.add(l)
                            nhits += 1
                        j = s.find(pat, j + 1)
        for l in ls:
            v = val(l)
            if v > best:
                best, arg = v, (k0, l)
    return best, arg, nhits


def brute(N):
    """max k0 + k1 over odd n < 2^N by iterating the map (tiny N only)"""
    best = 0
    for n in range(1, 2 ** N, 2):
        x = n
        k = []
        for _ in range(2):
            r = 0
            while x % 2 == 1:
                x = (3 * x + 1) // 2
                r += 1
            k.append(r)
            while x % 2 == 0:
                x //= 2
        best = max(best, sum(k))
    return best


if __name__ == "__main__":
    for N in map(int, sys.argv[1:]):
        t = time.time()
        B, arg, h = bound(N)
        print(N, B, arg, "hits", h, "%.1fs" % (time.time() - t), flush=True)
