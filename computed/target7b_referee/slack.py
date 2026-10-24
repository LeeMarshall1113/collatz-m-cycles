"""how far each used grid value of the worst m=121 shape could rise before ratio >= 1"""
import mychain as C
b2, b3 = C.load_grids()
K = 27444133206411171953; p = C.pfor(K); m = 121
r = C.check_shape(m, K, p, C.MinGrid(b2), C.MinGrid(b3))
print('base', float(r['ratio']))
def ratio(d2, d3):
    return C.check_shape(m, K, p, C.MinGrid(d2), C.MinGrid(d3))['ratio']
for kind, used in (('B3', sorted(r['u3'])), ('B2', sorted(r['u2']))):
    res = []
    for N in used:
        lo, hi = 0, 1
        while True:
            d2, d3 = dict(b2), dict(b3)
            (d3 if kind == 'B3' else d2)[N] += hi
            if ratio(d2, d3) >= 1: break
            lo, hi = hi, hi * 2
            if hi > 10 ** 6: break
        while hi - lo > 1:
            mid = (lo + hi) // 2
            d2, d3 = dict(b2), dict(b3)
            (d3 if kind == 'B3' else d2)[N] += mid
            if ratio(d2, d3) >= 1: hi = mid
            else: lo = mid
        res.append((N, lo))
    print(kind, 'max tolerated increase per point:', res, flush=True)
