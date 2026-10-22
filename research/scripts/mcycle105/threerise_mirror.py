"""Python mirror of Collatz/ThreeRiseCheck.lean (the AllTriples checker), for testing and cost estimates.

usage: python threerise_mirror.py test NMAX       compare with brute force for N = 2..NMAX
       python threerise_mirror.py run N B [E1]     run the checker, print the triple count"""
import sys

def low_scan(x, f, s):
    for _ in range(f):
        if (x >> s) & 1:
            return s
        s += 1
    return s

def match_mask(M, E, X, P):
    r = M
    for _ in range(E):
        r &= X ^ (0 if P & 1 else M)
        X >>= 1; P >>= 1
    return r

STATS = {'triples': 0, 'direct': 0}

def d_ok(D, A2, W2, y, c, L2):
    STATS['direct'] += 1
    J = D * L2
    return J <= W2 and A2 <= (y + c * (J - L2)) % J

def d_range(D, A2, W2, y, c, cnt, L2):
    for _ in range(cnt):
        if not d_ok(D, A2, W2, y, c, L2):
            return False
        L2 *= 2
    return True

def fallback(D, A2, W2, y, c, f, mm):
    for _ in range(f):
        if mm == 0:
            return True
        Pt = mm & (mm ^ (mm - 1))
        if not ((Pt & (Pt - 1)) == 0 and 1 <= Pt and (mm & Pt) == Pt and d_ok(D, A2, W2, y, c, A2 // Pt)):
            return False
        mm ^= Pt
    return mm == 0

def pat_core(D, A2, W2, y, c, E1, L, M, X, P, s):
    if s < E1:
        return (((P >> s) & 1) == 1 and P % 2**s == 0 and
                fallback(D, A2, W2, y, c, L, match_mask(M, E1 - (s + 1), X >> (s + 1), P >> (s + 1)) & (M ^ 1)))
    return P == 0 and fallback(D, A2, W2, y, c, L,
                               (match_mask(M, E1, X, 0) | match_mask(M, E1, X, 2**E1 - 1)) & (M ^ 1))

def pat_ok(D, A2, W2, y, c, A, E1, qmin):
    L = A - qmin + 1 if A >= qmin else 1
    P = (y >> A) % 2**E1
    return pat_core(D, A2, W2, y, c, E1, L, 2**L - 1, c % 2**(A + E1), P, low_scan(P, E1, 0))

def nsub(a, b):
    return a - b if a >= b else 0

def t_core(E1, W, A, A2, W2, y, c, p, D, t, qmin):
    q0 = max(A, p + 1)
    return (((y >> A) >> t) & 1 == 1 and
            d_range(D, A2, W2, y, c, nsub(A + t + 1, q0), 2**q0) and
            d_range(D, A2, W2, y, c, nsub(min(A, qmin), p + 1), 2**(p + 1)) and
            (True if A <= qmin else (A + E1 <= W and pat_ok(D, A2, W2, y, c, A, E1, qmin))))

def t_ok(B, E1, W, A, A2, W2, k0, x, l0, k1, c):
    STATS['triples'] += 1
    p = l0 + k1
    y = (x + c * 2**p) % W2
    E = max(1, nsub(B + 1, k0 + k1))
    return t_core(E1, W, A, A2, W2, y, c, p, 2**E, low_scan(y >> A, W, 0), max(p + 1, nsub(A + E1, E)))

def k1_loop(B, E1, W, i3, A, A2, W2, k0, x, l0, cnt, k1, c):
    for _ in range(cnt):
        c = c * i3 % W2
        if not t_ok(B, E1, W, A, A2, W2, k0, x, l0, k1, c):
            return False
        k1 += 1
    return True

def l_body(B, E1, W, i3, A, A2, W2, k0, c0, l0):
    x = c0 * nsub(W2 + 1, 2**l0) % W2
    t = low_scan(x >> A, W, 0)
    return (((x >> A) >> t) & 1 == 1 and l0 <= A + t and
            k1_loop(B, E1, W, i3, A, A2, W2, k0, x, l0, nsub(A + t, l0), 1, c0))

def k_ok(N, B, E1, W, i3, k0, c0):
    A = N - k0 if k0 < N else 1
    W2 = 2**W
    t = low_scan(c0 >> A, W, 0)
    if not (((c0 >> A) >> t) & 1 == 1):
        return False
    for l0 in range(1, A + t + 1):
        if not l_body(B, E1, W, i3, A, 2**A, W2, k0, c0, l0):
            return False
    return True

def Wof(N, B, E1):
    return 2 * B + 2 * E1 + 64

def all_triples(N, B, E1=16, W=None):
    W = W or Wof(N, B, E1)
    i3 = (2**(W + 1) + 1) // 3
    assert 3 * i3 % 2**W == 1
    c = 1
    for k0 in range(1, N + 1):
        c = c * i3 % 2**W
        if not k_ok(N, B, E1, W, i3, k0, c):
            return False
    return True

def brute(N):
    def runs(n):
        tot = 0
        for _ in range(3):
            k = 0
            while n & 1:
                n = (3 * n + 1) // 2; k += 1
            tot += k
            while n % 2 == 0:
                n //= 2
        return tot
    return max(runs(n) for n in range(1, 2**N, 2))

if __name__ == "__main__":
    if sys.argv[1] == "test":
        for N in range(2, int(sys.argv[2]) + 1):
            b = brute(N)
            ok1 = all_triples(N, b)
            ok0 = all_triples(N, b - 1)
            print(N, b, ok1, ok0, flush=True)
            assert ok1 and not ok0
    else:
        N, B = int(sys.argv[2]), int(sys.argv[3])
        E1 = int(sys.argv[4]) if len(sys.argv) > 4 else 16
        print(N, B, all_triples(N, B, E1), STATS)
