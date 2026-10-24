# Target 7c: independent proofs of Theorem 1 and Lemma 3S, and the logic of "no m-cycle for m ≤ 121"

Second independent referee. I wrote this without reading `target7_threerise/referee/` or
`target7b_referee/`. Labels: [proved here] = full proof below. [external] = an input taken from the
literature or from Alick's Lean repo (I read the Lean source; I did not run it). [computed] = done
by the scripts in this directory, exact arithmetic.

## 0. Setting and notation

- T(n) = (3n+1)/2 for odd n, T(n) = n/2 for even n. T extends to the 2-adic integers Z_2 by the
  same formula.
- For x ∈ Z_2 the *parity vector* of x is (x_i mod 2)_{i≥0}, where x_i = T^i(x).
- **Fact P** (Terras; standard). For every L ≥ 0 the map x ↦ (first L parities of x) induces a
  bijection Z/2^L → {0,1}^L.
  *Proof.* Induct on L. If x ≡ y mod 2^{L+1} they have the same parity, and T(x) ≡ T(y) mod 2^L,
  because both (3x+1)/2 and x/2 lose exactly one power of 2. Hence the first L+1 parities depend
  only on x mod 2^{L+1}. Injectivity: suppose x and y have the same first L+1 parities. Then
  x ≡ y mod 2. By induction T(x) ≡ T(y) mod 2^L. Since T is affine with slope 3/2 or 1/2 on each
  parity class, this gives x ≡ y mod 2^{L+1}. Bijectivity follows by counting. ∎
- **Runs.** An odd n ≥ 1 has a block (k, l): n+1 = 2^k a with a odd, then
  T^j(n) + 1 = 3^j 2^{k−j} a for j ≤ k. So exactly k odd steps occur, and T^k(n) = 3^k a − 1 is even
  and positive. Then exactly l = v_2(3^k a − 1) ≥ 1 even steps follow, reaching
  n' = (3^k a − 1)/2^l, which is odd. Write k = orun(n), l = erun(n) and n' = nextMin(n).
  This is Alick's `block_eq`.
- For odd n ≥ 1, (k0, l0, k1, l1, k2, …) are the run lengths of n, n' = nextMin n, n'' = nextMin n'.
  The r-rise bound is B_r(N) = max over odd n < 2^N of k0 + … + k_{r−1}.
- u_k = (2/3)^k ∈ Z_2, so v_2(u_k) = k. For x ∈ Z_2 that is not a non-negative integer below 2^N,
  z_N(x) is the least i ≥ N such that bit i of x is 1.

## 1. Theorem 1 (exact 2-adic form of B3) [proved here]

**Theorem 1.** For σ = (k0, l0, k1, l1) ∈ Z_{≥1}^4, put K = k0 + k1, λ = l0 + l1, P2 = K + λ, and

    ν(σ) = −1 + u_{k0}(1 − 2^{l0}) + 2^{l0} u_K (1 − 2^{l1}) ∈ Z_2.

Then B3(N) = max{ z_N(ν(σ)) − λ : σ ∈ Z_{≥1}^4, z_N(ν(σ)) > P2 }, and the maximum is attained.

**Lemma 1.1.** The parity vector of ν(σ) is 1^{k0} 0^{l0} 1^{k1} 0^{l1} 1^∞.

*Proof.*
1. ν + 1 = 2^{k0} · 3^{−k0} · c, with c = (1 − 2^{l0}) + 2^{l0} u_{k1}(1 − 2^{l1}). Here c is odd,
   because l0 ≥ 1 and k1 ≥ 1, so the first term is odd and the second is even. So
   ν + 1 = 2^{k0} a with a = 3^{−k0}c ∈ Z_2^× odd.
2. As in the integer case, T^j(ν) + 1 = 3^j 2^{k0−j} a. So ν makes exactly k0 odd steps and
   T^{k0}(ν) = c − 1 = 2^{l0}(−1 + u_{k1}(1 − 2^{l1})).
3. The bracket is odd, since u_{k1} is even. So exactly l0 even steps follow, reaching
   ν1 = −1 + u_{k1}(1 − 2^{l1}).
4. The same computation with (k1, l1) and second term 0 gives k1 odd steps to
   (1 − 2^{l1}) − 1 = −2^{l1}. Then exactly l1 even steps reach −1.
5. T(−1) = −1 is odd, so the vector continues 1^∞. ∎

**Lemma 1.2.** Let j ≥ 1 and let n be odd. Then n has (k0, l0, k1, l1) = σ and k2 ≥ j if and only
if n ≡ ν(σ) (mod 2^{P2+j}).

*Proof.* The condition "the runs are exactly σ and k2 ≥ j" says that the first P2 + j parities of n
are the word w = 1^{k0}0^{l0}1^{k1}0^{l1}1^j. The trailing 1^j (j ≥ 1) closes the run l1, so each
of the four runs is pinned exactly. By Lemma 1.1, ν has this prefix. By Fact P, exactly one class
mod 2^{P2+j} has prefix w. ∎

**Lemma 1.3.** Let C be a class mod 2^L containing the odd 2-adic integer ν. Then C meets
{1, 3, …, 2^N − 1} if and only if L ≤ z_N(ν).

*Proof.*
- **Case L ≤ N.** The representative ν mod 2^L lies in [0, 2^N), and it is odd, so it is ≥ 1.
  Also z_N(ν) ≥ N ≥ L.
- **Case L > N.** The class meets [0, 2^N) iff its least non-negative representative ν mod 2^L
  is < 2^N. That holds iff bits N, …, L−1 of ν vanish, i.e. iff z_N(ν) ≥ L.

z_N(ν) is finite: if all bits ≥ N of ν vanished, ν would be a positive integer whose parity
vector ends in 1^∞. That is impossible, because v_2(ν+1) would be infinite. ∎

*Proof of Theorem 1.*
- Fix σ. By Lemmas 1.2 and 1.3, the largest k2 achievable by an odd n < 2^N with runs σ is
  j*(σ) = z_N(ν) − P2. Such n exist iff j*(σ) ≥ 1, because every odd n has k2 ≥ 1. The best total
  for σ is then K + j* = z_N(ν) − λ.
- Every odd n < 2^N has some σ. Its total is ≤ the best total for its σ, so B3(N) ≤ the max.
- Conversely, each feasible σ is realised by an actual n < 2^N.
- The set of values is a subset of the finite set {k0 + k1 + k2 of odd n < 2^N}. So the max exists
  and equals B3(N). ∎

*The r = 2 case.* Drop the second block: α = −1 + u_{k0}(1 − 2^{l0}), and
B2(N) = max{ z_N(α) − l0 : z_N(α) > k0 + l0 }.

**Verdict on WRITEUP §1.2.** The proof there is correct and essentially this one. Two places are
under-justified, though not wrong:
1. It never says why z_N(ν) is finite, or why the max is a max.
2. In (ii) it uses the bijection of Fact P without stating that ν's prefix is the word, which is
   Lemma 1.1.

I found no error.

**Independent computational check** [computed, `b3crt.py`]. This uses a different decomposition
from anything in the repo. The first block is solved in the integers by CRT:
- n1 runs over odd n1 ≡ −2^{−l0} (mod 3^{k0}) with n1 ≤ ⌊(3^{k0}2^{N−k0} − 1)/2^{l0}⌋;
- a = (2^{l0}n1 + 1)/3^{k0} is then automatically odd;
- the rest is a 2-adic condition on t = (n1 − r)/3^{k0}.

The method contains no z_N and no windows.

| check | result |
|---|---|
| vs literal brute force (both B2 and B3), N = 2..22 | 21/21 identical |
| B3(73) | 85 (grid 85), witness simulated |
| B3(117) | 130 (grid 130), witness simulated |
| B3(194), B3(203) | see §5 |
| B2 at 72, 190, 799 | equal to the grid |
| B2 at the 14 small grid_own points listed in §4 G3 | true B2 is 1–2 **below** the grid. That is conservative, and was confirmed by a second, 2-adic method |

## 2. Lemma 3S (three steps) and the r-step version [proved here]

**Lemma 2.1 (one block).** Let n be odd with block (k, l) and n' = nextMin n. Then
2^{k+1}(n' + 1) ≤ 3^k(n + 1) + 2^k.

*Proof.* Put n + 1 = 2^k a and 2^l n' = 3^k a − 1 with l ≥ 1. Then

    2^l · [3^k a + 1 − 2(n' + 1)] = 2^l 3^k a + 2^l − 2·3^k a + 2 − 2^{l+1} = (2^l − 2)(3^k a − 1) ≥ 0.

So 2(n' + 1) ≤ 3^k a + 1. Multiplying by 2^k gives the claim. ∎

**Lemma 2.2 (r blocks).** Let n = m_0, m_1, …, m_r be successive minima (m_{i+1} = nextMin m_i), with
rises k_0, …, k_{r−1}. Put s_i = k_0 + … + k_{i−1} and s = s_r. Then

    2^r 2^s (m_r + 1) ≤ 3^s (n + 1) + Σ_{i=0}^{r−1} 2^i 3^{s − s_{i+1}} 2^{s_{i+1}}.

*Proof.* Induct on r; r = 1 is Lemma 2.1. For the step from r to r+1:
1. Apply Lemma 2.1 to m_r → m_{r+1}: 2^{k_r+1}(m_{r+1} + 1) ≤ 3^{k_r}(m_r + 1) + 2^{k_r}.
2. Multiply by 2^r 2^{s_r} > 0.
3. Bound 2^r 2^{s_r}(m_r + 1) by the induction hypothesis. Every term gets multiplied by 3^{k_r},
   and the new term 2^r 2^{s_{r+1}} appears. ∎

**Corollary 2.3.** Dividing the error terms by 3^s gives Σ_i 2^i (2/3)^{s_{i+1}}. Since
s_{i+1} ≥ i + 1, this is ≤ Σ_{i<r} 2^i (2/3)^{i+1} = 2((4/3)^r − 1) =: c_r, so

    x_r ≤ x_0 + (δ − 1)s − r + log_2(1 + c_r/(n+1)) ≤ x_0 + (δ − 1)s − r + c_r/((n+1) ln 2),

with δ = log_2 3, x_0 = log_2(n+1) and x_r = log_2(m_r + 1).
- For r = 3: c_3 = 74/27, and (74/27)/ln 2 = 3.954… < 4. This is Lemma 3S as stated.
- For r = 2: c_2 = 14/9, so the coefficient is 2.24 < 6. This is weaker than Alick's
  `logb_two_step`, which uses 6/(n+1); I read that statement and it is consistent.
- If n < 2^N then s ≤ B_r(N), by definition.

**Verdict on WRITEUP §2.** The three-step chain displayed in step 2 is correct line by line (I
redid it). The bound 74/27 < 3 and the log step are correct, and so is the general-r form with
2.9(4/3)^r. No errors.

## 3. The chain argument (glue) [proved here, given the external inputs]

**External inputs.**
- **E1 (Barina).** Every n ≤ 2^71 reaches 1, so every element of a non-trivial positive cycle is
  ≥ X0 = 2^71 + 1. This is computational and not formally verified.
- **E2 (Hercher, Theorem 21, two-element form).** This is Alick's `theorem21_two`. I read the Lean
  statement and found no `sorry` or `axiom` in the Collatz/ sources; I did not run the build or
  the axiom audit.

  The statement: for a cycle with m = numLocalMin local minima, K odd steps and period p, a real
  X ≤ every element, and 1 ≤ m2 ≤ m,

      Λ := p ln 2 − K ln 3 < (m − m2)/X + 1/(2^v − 1) + (m2 − 1)/(2^τ − 1),

  with v = m2 K / (m Σ_{d<m2} δ^d) and τ = m2 K / (m(1 + Σ_{d<m2−1} δ^d)). Any integers
  1 ≤ N ≤ v and 1 ≤ M ≤ τ may replace v and τ.

  The repo takes N with N·m·G_DU(m2) ≤ m2 K, where DU = 1.58496250072116 > δ. That implies
  N ≤ v. Note it is **not literally** an instance of `lambda_lt_two`, which is packaged with
  `deltaUp` = 1.584962501. A larger deltaUp gives a stronger side condition, and the repo's N can
  exceed what `lambda_lt_two` allows. The repo's use rests on `theorem21_two` itself. That is
  sound, but the citation should say so (gap G1, cosmetic).
- **E3 (Rhin, via Simons–de Weger Lemma 12).** For every non-trivial positive cycle,
  Λ > exp(−13.3(0.46057 + ln K)). Alick's Lean repo carries this only as the hypothesis
  `RhinBound`. I could not re-read the original paper here.
- **E4 (Remark 7).** Λ < m/X. This is `ratioIn_of_crude`, formalised.

**Theorem 3.1.** Let m ≥ 1, and let (K, p) be the shape of a hypothetical non-trivial cycle with
m minima. Let g2 and g3 be finite tables with B2(N) ≤ g2(N) and B3(N) ≤ g3(N) at their grid
points. Define rationals Y_0, …, Y_{m−1} as follows:
- Y_0 ≥ log_2⌈Ub⌉, where Ub = (m − m2)/(Λ_lo − tail) for some admissible m2, and Λ_lo ≤ Λ is
  certified;
- Y_{t} ≥ min{ D·Y_{t−1}, Y_{t−2} + (D − 1)·b2(Y_{t−2}) − 2 + 6/2^71,
  Y_{t−3} + (D − 1)·b3(Y_{t−3}) − 3 + 4/2^71 };
- D ≥ δ, and b_r(y) = min{ g_r(N) : N ≥ ⌈y⌉ } (that term is dropped if the set is empty).

If Σ Y_t < K, no such cycle exists.

*Proof.*
1. Let n_0 be the least element. It is a local minimum (`exists_least_rotation`; directly: if
   n_0 were even, n_0/2 would be smaller; if its predecessor q were odd, n_0 = (3q+1)/2 > q).
2. Let n_t = nextMin^t(n_0), x_t = log_2(n_t + 1) and k_t = orun(n_t), for t = 0..m−1. These are
   the m minima once around the cycle.
3. Lemma 8: K = Σ k_t, and k_t ≤ x_t because 2^{k_t} divides n_t + 1. So Σ x_t ≥ K.
4. E2 with X = n_0 gives n_0 < Ub, so n_0 + 1 ≤ ⌈Ub⌉ and x_0 ≤ Y_0.
5. Induction on t, assuming x_j ≤ Y_j for all j < t:
   - Lemma 20 gives x_t ≤ δ x_{t−1} ≤ D Y_{t−1}. (Directly: n'+1 ≤ (3^k a + 1)/2 ≤ 3^k a ≤ (n+1)^δ.)
   - If N ≥ ⌈Y_{t−2}⌉ is a grid point, then x_{t−2} ≤ N, so n_{t−2} < 2^N and
     k_{t−2} + k_{t−1} ≤ B2(N) ≤ g2(N).
     The two-step lemma (with n_{t−2} > 2^71) then gives
     x_t ≤ Y_{t−2} + (δ − 1)g2(N) − 2 + 6/2^71.
   - The three-step case is the same, using Corollary 2.3.
   - So x_t is ≤ each candidate, hence ≤ their min, hence ≤ Y_t.
   - The windows t−2..t and t−3..t never wrap, so no cyclic argument is needed.
6. Σ x_t ≤ Σ Y_t < K contradicts step 3. ∎

**Glue verdict.**
- The repo's `chain3.shape_check3` is exactly Theorem 3.1. It works in 2^{−64} units with upward
  rounding. Y_0 = ⌈2^{64} log_2 ⌈Ub⌉⌉ comes from an mpmath interval upper endpoint, and the
  2^{−64}·1 slack absorbs 6/2^71 and 4/2^71.
- `Grid.B_for` is a suffix minimum over N ≥ ⌈Y/2^S⌉. That is valid without any monotonicity
  of B_r, so no unproved monotonicity is used anywhere in the chain.
- The final comparison is an exact Fraction.
- I found no float in a load-bearing place of the chain.

**Shape completeness.**
1. Every shape satisfies 0 < p − Kδ < Λ/ln 2, by E4 and since Λ > 0 for a cycle. So p = ⌈Kδ⌉.
2. **Rhin ceiling.** E2 with m2 = m gives Λ < m·2^{2−K/G(m)}. Combined with E3, this excludes every
   K with g(K) = (K/G − 2)ln 2 − ln m − 13.3(0.46057 + ln K) ≥ 0.
   - g is increasing for K > 13.3 G/ln 2.
   - The repo finds Kceil by interval bisection above that point. That is rigorous.
   - I re-verified g(Kceil) ≥ 0 with my own rational log bounds (`enum7c.rhin_check`), at m = 104
     and 110.
   - Note: using G with DU ≥ δ only shrinks N, so it is conservative.
3. **Strip and filter.** `common.survives` is a conservative test. It uses DLO/DHI at 1e−100,
   L2LO, NCAP = 400, and a min over m2. Capping N or M only weakens the bound.
4. **`fastshapes`** uses floats only to compute an upper bound L for lam_bound on each K interval,
   with a 1e−9 inflation. Every candidate then passes the exact `survives`.
   - The merge step assumes lam_bound is non-increasing in K. That holds exactly: N and M are
     non-decreasing in K, so each m2-term is non-increasing.
   - The float slop (< 1e−15) is far inside the 1e−9 inflation. So this float is safe but
     load-bearing in principle (gap G2, minor: it would be cleaner as a Fraction).
   - The box bounds (x range from corners, y range with pad 2, K′ range) are correct supersets.
     I checked the algebra x = s(K′e_{n+1} − e′q_{n+1}).
5. **Independent enumeration** [computed, `enum7c.py`]. This uses a different algorithm: a
   three-gap / Slater return-time walk along the Remark-7 strip, with my own constants and filter.
   - Self-test against brute force: identical.
   - m = 104: 74434 strip points (the same number target 7 reports) and 138 survivors, a set
     **identical** to fastshapes.
   - m = 110: see §5.

## 4. Gaps and remarks on WRITEUP.md (target 7 and 7b)

- **G1** (cosmetic): cite `theorem21_two`, not `lambda_lt_two`. The repo's DU differs from Lean's
  `deltaUp` (§3, E2).
- **G2** (minor): the float lam_bound in `fastshapes.intervals` is safe, but it would be cleaner
  in exact arithmetic.
- **G3** (documentation): `grid_own.json` B2 values are **upper bounds, not exact values**. True B2 is
  1–2 smaller at 94, 103, 115, 116, 119, 120, 123, 125, 182, 191, 193, 194, 195 and 220. This was
  checked by two independent methods. It is harmless (conservative), but "B2 exact" should not
  be claimed for grid_own.
- **G4** (reproducibility): `fastshapes`/`shapes` crash on this box's Python 3.14 with gmpy2
  (SystemError: "Object does not appear to be Fraction"). mpmath's gmpy backend hands mpz to
  Fraction. Run with `MPMATH_NOGMPY=1`.
- **G5** (robustness, not an error): at m = 121 the worst shape is insensitive to a +6 error at
  any single B3 grid point. However, a *uniform* +4 on all B3 values gives ratio 1.008, and +7
  gives 1.598. B2 tolerates a uniform +1000 or so before failing. So the claim depends on the B3
  grid being right to within about 3 across the board. Exactness of `b3join` matters, which is
  why independent B3 spot checks at large N would be the most valuable remaining check.
- Lemma 3S and Theorem 1 contain no errors.
- WRITEUP 7 §1.3 (b3.py region split) and 7b §1 (b3join) are algorithm descriptions, not proofs.
  I did not audit their carry logic; I spot-checked their outputs instead.

## 5. Recomputation results [computed]

See the final report and `*.out` files in this directory.
