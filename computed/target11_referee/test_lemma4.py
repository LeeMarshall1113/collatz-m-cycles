"""numerical sanity of the r-step lemma (r = 4): 2^4 2^s (m4+1) <= 3^s (n+1) + sum_i 2^i 3^(s-s_{i+1}) 2^(s_{i+1}),
and the logged form with c_4 = 350/81, on random odd n (small and ~2^300) and on structured n = 2^k - 1 patterns"""
import random, math
from fractions import Fraction as F
def nxt(n):
    x = n + 1; k = (x & -x).bit_length() - 1
    y = 3 ** k * (x >> k) - 1; l = (y & -y).bit_length() - 1
    return k, y >> l
rnd = random.Random(7); worst = F(0); cnt = 0
for trial in range(200000):
    b = rnd.choice([8, 20, 64, 300])
    n = rnd.getrandbits(b) | 1
    if trial % 7 == 0:
        n = (1 << rnd.randint(2, 200)) * rnd.getrandbits(5) - 1 if rnd.random() < .5 else n
        if n <= 0 or n % 2 == 0: continue
    ks, ms = [], [n]
    for _ in range(4):
        k, ms_ = nxt(ms[-1]); ks.append(k); ms.append(ms_)
    s_ = [0]
    for k in ks: s_.append(s_[-1] + k)
    s = s_[4]
    lhs = 16 * 2 ** s * (ms[4] + 1)
    rhs = 3 ** s * (n + 1) + sum(2 ** i * 3 ** (s - s_[i + 1]) * 2 ** s_[i + 1] for i in range(4))
    assert lhs <= rhs, n
    err = F(rhs, 3 ** s * (n + 1)) - 1          # must be <= c_4/(n+1)
    assert err * (n + 1) <= F(350, 81)
    worst = max(worst, err * (n + 1)); cnt += 1
print(f"{cnt} odd n: 4-step lemma holds; max (n+1)*err = {float(worst):.4f} <= c_4 = {350/81:.4f}; c_4/ln2 = {350/81/math.log(2):.3f} < 2^7")
