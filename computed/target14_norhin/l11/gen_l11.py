"""Gelfond L11 generator: 215-digit enclosure of log_2 3 and Farey segments up to 10^100.
Mirrors Lean's logSum exactly (rational series), cross-checks with mpmath and an independent
Machin-type atanh series."""
from fractions import Fraction as F
from mpmath import mp, mpf, log, floor

D = 215            # digits of the enclosure
N2 = 730           # logSum (1/2) N2 : error <= 2^-N2   (~ 1e-216.7)
N3 = 460           # logSum (1/3) N3 : error <= 1/(2*3^N3)  (~ 1e-215.5)
assert F(1, 2**N2) < F(1, 10**(D+1)) and F(1, 2*3**N3) < F(1, 10**(D+1))


def logSum(x, n):
    s = F(0)
    for i in range(n):
        s += x**(i+1) / (i+1)
    return s


S2 = logSum(F(1, 2), N2)
S3 = logSum(F(1, 3), N3)
e2 = F(1, 2**N2)
e3 = F(1, 2*3**N3)
l2, u2 = S2 - e2, S2 + e2
l3, u3 = S2 + S3 - e2 - e3, S2 + S3 + e2 + e3
lo = l3 / u2
hi = u3 / l2
LO = (lo.numerator * 10**D) // lo.denominator           # floor
HI = -((-hi.numerator * 10**D) // hi.denominator)        # ceil
deltaLo = F(LO, 10**D)
deltaHi = F(HI, 10**D)
assert deltaLo * u2 < l3 and u3 < deltaHi * l2          # the two Lean kernel checks (strict)
print("width", float(deltaHi - deltaLo), "digits", len(str(LO)))

# --- cross-check 1: mpmath at 400 digits
mp.dps = 400
d = log(3) / log(2)
assert mpf(LO) / mpf(10)**D < d < mpf(HI) / mpf(10)**D


# --- cross-check 2: independent Machin-type atanh series in exact integers
def atanh_inv(n, P):  # atanh(1/n) * 10^P, error a few ulps
    s = 0
    t = 10**P // n
    k = 1
    n2 = n*n
    while t:
        s += t // k
        t //= n2
        k += 2
    return s


P = 320
ln2 = 18*atanh_inv(26, P) - 2*atanh_inv(4801, P) + 8*atanh_inv(8749, P)
ln3 = 2*atanh_inv(2, P)
r = F(ln3, ln2)
assert abs(r - F(LO+HI, 2*10**D)) < F(1, 10**(D-1)), "independent check failed"
assert deltaLo < F(ln3 - 2000, ln2 + 2000) and F(ln3 + 2000, ln2 - 2000) < deltaHi
print("cross-checks ok")

# --- convergents of delta
x = d
h0, k0, h1, k1 = 0, 1, 1, 0
conv = []
for i in range(400):
    a = int(floor(x))
    x = 1/(x-a)
    h0, k0, h1, k1 = h1, k1, a*h1+h0, a*k1+k0
    conv.append((h1, k1))
segs = []
for (P1, Q1), (P2, Q2) in zip(conv, conv[1:]):
    if F(P1, Q1) < F(P2, Q2):
        a, b, c, dd = P1, Q1, P2, Q2
    else:
        a, b, c, dd = P2, Q2, P1, Q1
    assert c*b - a*dd == 1
    segs.append((a, b, c, dd))
    if b+dd > 10**100:
        break
C = 1000
LN2 = F(6931471803, 10**10)
L = 10**36
mnscore = None
used = []
for (a, b, c, dd) in segs:
    if b+dd <= L:
        continue
    assert F(a, b) < deltaLo and deltaHi < F(c, dd)
    mg = min(deltaLo - F(a, b), F(c, dd) - deltaHi)
    score = LN2 * L * mg * 2**C
    assert mg > 0 and score > 1, (a, b, c, dd, float(mg))
    mnscore = score if mnscore is None else min(mnscore, score)
    used.append((a, b, c, dd))
    L = b+dd
assert L > 10**100
print("segments total", len(segs), "used", len(used),
      "min score log10", float(mp.log10(mpf(mnscore.numerator)/mnscore.denominator)))

R = 'C:/Users/hackathon/Documents/GitHub/collatz-m-cycles-release/'
out = open(R+'computed/target14_norhin/l11/LogTwoThreeBounds215.tmpl', encoding='utf8').read()
out = out.replace('@D@', str(D)).replace('@N2@', str(N2)).replace('@N3@', str(N3)) \
         .replace('@LO@', str(LO)).replace('@HI@', str(HI))
open(R+'Collatz/LogTwoThreeBounds215.lean', 'w', encoding='utf8').write(out)

seg = open(R+'computed/target14_norhin/l11/MidRangeData.tmpl', encoding='utf8').read()
lst = ",\n".join("  \u27e8%d, %d, %d, %d\u27e9" % s for s in used)
seg = seg.replace('@N@', str(len(used))).replace('@LIST@', lst)
open(R+'Collatz/MidRangeData.lean', 'w', encoding='utf8').write(seg)
print("written")
