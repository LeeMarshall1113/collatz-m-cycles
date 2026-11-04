# Independent proof: Lemma 2.2 (r blocks), Corollary 2.3 (c_r, c_4 = 350/81), and the chain theorem with r <= 4 windows

Written 2026-11-03 as a clean-room referee proof for the m <= 127 four-rise argument. Proof work only; no compute
beyond sub-second Python sanity checks.

## 0. Clean-room note (what was read, and when)

Before writing sections 1-4 below I read only `METHOD.md` lines 50-139 and 169-198 of the release repository.
Those ranges are the setting (section 1), section 2 and section 4 of METHOD.md, and part of section 3. Two
departures from a strict "statements only" reading, recorded so the reader can weigh them:

* The read of lines 81-92 included the two-line proof of Lemma 2.1 and the one-sentence proof sketch of Lemma
  2.2 ("induction on r; multiply Lemma 2.1 by 2^r 2^(s_r), ..."). The read of lines 169-189 included the
  paragraph-long proof of Theorem 3.1. I saw both while reading the statements. The arguments below were
  worked out separately: each inequality was re-derived, and the hypotheses in section 3 were listed from the
  statement, not from that paragraph. Even so, the chain proof follows the same route as METHOD's sketch,
  because that route is the natural one. It is independent in checking, not in strategy.
* Lines 113-139 (Theorem 1 and Lemmas 1.1-1.3 with their proofs) were also in view. They are not used here.

`computed/target7c_proofs/PROOFS.md`, `collatz-loop/research/target10_rrise/WRITEUP.md`, all `.lean` files and all
code were opened **only after** sections 1-4 of this file had been written to disk. Section 5 is the comparison.

Sanity check (scratchpad script `l22check.py`, run with `/c/Python314/python`, under 1 s): Lemma 2.2 and the
error bound `<= c_r` were checked exactly for r = 1..6 on all odd n < 20000 and on 20000 random odd 90-bit n:
0 violations, equality in 29686 cases (all descents equal to 1, as predicted below). Lemma 20 in the form
`n'+1 <= (3/2)^k (n+1)` was checked too, with 0 violations. Exact c_r and c_r/ln 2 were computed for r <= 14.

## 1. Setting (as used here)

`T(n) = n/2` for even n and `(3n+1)/2` for odd n. For odd `n >= 1` write `n + 1 = 2^k a` with `a` odd and
`k >= 1`. Then `T^j(n) + 1 = 3^j 2^(k-j) a` for `0 <= j <= k`. (Induction: if `T^j(n)+1 = 3^j 2^(k-j) a` with
`j < k`, then `T^j(n)` is odd and `T^(j+1)(n) + 1 = (3 T^j(n) + 3)/2 = 3^(j+1) 2^(k-j-1) a`.) So
`T^j(n)` is odd for `j < k`, and `T^k(n) = 3^k a - 1` is even. Put `l = v2(3^k a - 1) >= 1` and
`n' = nextMin(n) = (3^k a - 1)/2^l`, which is odd. Also `n' >= 1`, since `3^k a >= 3`. Write `k = orun(n)`.
For `n >= 1` odd, the iterates `nextMin^i(n)` are therefore odd positive integers, defined for all `i >= 0`.

`delta = log2 3`. Throughout, `ln` is the natural log.

## 2. Lemma 2.1, Lemma 20, Lemma 2.2 and Corollary 2.3

**Lemma 2.1.** For odd `n >= 1` with `k = orun(n)` and `n' = nextMin(n)`:
`2^(k+1) (n'+1) <= 3^k (n+1) + 2^k`, with equality iff the descent `l` equals 1.

*Proof.* `2(n'+1) = (3^k a - 1)/2^(l-1) + 2 <= (3^k a - 1) + 2 = 3^k a + 1`. This uses `l >= 1` and
`3^k a - 1 > 0`, and it is an equality iff `l = 1`. Multiply by `2^k > 0` and use `2^k a = n+1`. []

**Lemma 20 (one-step growth; independent proof).** For odd `n >= 1`: `log2(n'+1) <= delta log2(n+1)`.

*Proof.* By the proof above, `2(n'+1) <= 3^k a + 1 <= 2 * 3^k a`, so `n'+1 <= 3^k a = (3/2)^k (n+1)`. Since
`2^k` divides `n+1`, `2^k <= n+1`, so `(3/2)^k = 2^(k(delta-1)) <= (n+1)^(delta-1)`, because `delta - 1 > 0`.
Hence `n'+1 <= (n+1)^delta`. []

(METHOD treats Lemma 20 as an external Lean input. The two-line proof above makes the chain argument
self-contained on paper.)

**Lemma 2.2 (r blocks).** Let `r >= 1`, let `m_0 = n` be an odd positive integer, and let `m_(i+1) = nextMin(m_i)`.
Put `k_i = orun(m_i)` for `0 <= i < r`, `s_0 = 0`, `s_i = k_0 + ... + k_(i-1)` and `s = s_r`. Then

    2^r 2^s (m_r + 1)  <=  3^s (n+1) + sum_{i=0}^{r-1} 2^i 3^(s - s_(i+1)) 2^(s_(i+1)).          (L_r)

Equality holds iff every one of the r descents equals 1.

*Proof.* Induction on `r`.

`r = 1`: `s = s_1 = k_0`, and the sum has the single term `2^0 3^0 2^(k_0)`. So (L_1) reads
`2^(k_0+1)(m_1+1) <= 3^(k_0)(n+1) + 2^(k_0)`, which is Lemma 2.1 for `m_0`.

`r -> r+1`: Write `s = s_r` and `s' = s_(r+1) = s + k_r`. Lemma 2.1 for `m_r` gives
`2^(k_r+1)(m_(r+1)+1) <= 3^(k_r)(m_r+1) + 2^(k_r)`. Multiply by `2^r 2^s > 0`:

    2^(r+1) 2^(s') (m_(r+1)+1) <= 3^(k_r) [2^r 2^s (m_r+1)] + 2^r 2^(s').

Bound the bracket by (L_r), and use `3^(k_r) >= 0`:

    <= 3^(s')(n+1) + sum_{i<r} 2^i 3^(s' - s_(i+1)) 2^(s_(i+1)) + 2^r 3^(s' - s_(r+1)) 2^(s_(r+1)).

The last term is the `i = r` term of the sum in (L_(r+1)), since `s' - s_(r+1) = 0`. This is (L_(r+1)).

Equality: each step is an equality iff Lemma 2.1 is an equality for `m_r` (factor `2^r 2^s > 0`) and (L_r) is an
equality (factor `3^(k_r) > 0`). By induction this means all descents are 1. []

*Remarks.* (i) Only `m_0, .., m_(r-1)` odd and positive is used. Positivity follows from `n >= 1`.
(ii) No hypothesis links `m_0` to a cycle. The lemma holds for every odd `n >= 1`. (iii) Equality is attained
(see section 0), so (L_r) cannot be improved as an inequality in the `k_i` alone.

**Corollary 2.3.** In the setting of Lemma 2.2, put `c_r = 2((4/3)^r - 1)`, `x = log2(n+1)` and
`x_r = log2(m_r+1)`. Then

    m_r + 1 <= (3^s / 2^(r+s)) (n + 1 + c_r)                                                     (C1)
    x_r     <= x + (delta - 1) s - r + log2(1 + c_r/(n+1))
            <= x + (delta - 1) s - r + c_r / ((n+1) ln 2).                                        (C2)

*Proof.* Divide (L_r) by `2^r 2^s 3^s`:
`m_r + 1 <= (3^s/2^(r+s)) [ (n+1) + E ]`, with `E = sum_{i<r} 2^i (2/3)^(s_(i+1))`.
Each `k_j >= 1`, so `s_(i+1) >= i+1`. Since `0 < 2/3 < 1`, `(2/3)^(s_(i+1)) <= (2/3)^(i+1)`, and

    E <= sum_{i=0}^{r-1} 2^i (2/3)^(i+1) = (2/3) sum_{i=0}^{r-1} (4/3)^i = (2/3) ((4/3)^r - 1)/(4/3 - 1) = 2((4/3)^r - 1) = c_r.

This gives (C1). Take log2 of (C1). `log2(3^s/2^(r+s)) = delta s - r - s`, and
`log2(n+1+c_r) = x + log2(1 + c_r/(n+1))`. Finally `log2(1+u) = ln(1+u)/ln 2 <= u/ln 2` for `u > -1`. []

`E = c_r` exactly iff all `k_0..k_(r-1)` equal 1. So `c_r` is the best constant that depends on `r` alone.

**Numeric values (exact rationals).** `c_1 = 2/3`, `c_2 = 2(16/9 - 1) = 14/9`, `c_3 = 2(64/27 - 1) = 74/27`, and

    c_4 = 2(256/81 - 1) = 2 * 175/81 = 350/81 = 4.32098...

The check `(350/81)/ln 2 < 7`: it is equivalent to `ln 2 > 350/567 = 50/81 = 0.61728...`. The series
`ln 2 = 2 artanh(1/3) = 2 sum_{j>=0} 3^(-(2j+1))/(2j+1)` has positive terms, so its first two terms give
`ln 2 > 2(1/3 + 1/81) = 56/81 = 0.6913 > 50/81`.
So `(350/81)/ln 2 < (350/81)/(56/81) = 350/56 = 6.25 < 7`. The numeric value is `6.2339`. Likewise:
`(74/27)/ln 2 < (74/27)(81/56) = 222/56 = 3.964 < 4` (numeric 3.9541), and
`(14/9)/ln 2 < (14/9)(81/56) = 2.25 < 6` (numeric 2.2442).

**Use with Barina (E1).** Suppose `n > 2^71`, i.e. `n + 1 >= 2^71 + 2`. Then
`c_r/((n+1) ln 2) < (c_r/ln 2)/2^71`. That is `< 6/2^71` (r = 2), `< 4/2^71` (r = 3) and `< 7/2^71` (r = 4).
It is `< 2^-64 = 128/2^71` iff `c_r/ln 2 <= 128`, which holds exactly for `r <= 13`: `c_13/ln 2 = 118.57`,
`c_14/ln 2 = 159.05`. METHOD's "r <= 13" claim is correct and sharp.

**Lemma 3S integer form (side check).** For r = 3, (L_3) gives
`8 * 2^s (m_3+1) <= 3^s (n+1) + 3^s E` with `E <= 74/27 < 7`, so `8 * 2^s (m_3+1) <= 3^s (n+8)`. Then
`x_3 <= x + (delta-1)s - 3 + log2(1 + 7/(n+1)) <= x + (delta-1)s - 3 + (7/ln 2)/(n+1)`, and
`7/ln 2 = 10.1 < 14`. METHOD's Lean form is consistent with this.

## 3. The chain theorem (Theorem 3.1) with windows of 1 to 4 rises

### 3.1 Precise statement

**Hypotheses.**

* (H0) There is a positive integer cycle of `T`, other than `{1, 2}`, with `m` local minima (odd elements whose
  predecessor in the cycle is even), `K` odd steps and period `p`. `Lambda = p ln 2 - K ln 3`.
* (H1) E1: every element of the cycle exceeds `2^71`.
* (H2) E2 for this cycle, in the form: for every real `X` with `0 < X < min(cycle)`, and the chosen `m2` with
  `1 <= m2 <= m`, `Lambda < (m - m2)/X + tail`. Here `tail = 1/(2^v - 1) + (m2-1)/(2^tau - 1)`, with any
  integers `v, tau` that E2 allows for `(m, m2, K)`. (Only `X` strictly below the minimum is assumed. If E2 also
  holds at `X = min(cycle)`, the argument just gets shorter.)
* (H3) `Lambda_lo` is a **rational** number with `Lambda_lo <= Lambda`, and `Lambda_lo - tail > 0`.
  Put `Ub = (m - m2)/(Lambda_lo - tail)`.
* (H4) `D` is a real number (rational in practice) with `D >= delta`.
* (H5) For `r in {2, 3, 4}` (any subset may be used), `G_r` is a finite set of positive integers, and
  `g_r : G_r -> Z` satisfies `B_r(N) <= g_r(N)` for every `N in G_r`. Here
  `B_r(N) = max { orun(n) + orun(nextMin n) + ... + orun(nextMin^(r-1) n) : n odd, 1 <= n < 2^N }`.
  For real `y` put `b_r(y) = min { g_r(N) : N in G_r, N >= ceil(y) }`, or `b_r(y) = +infinity` if that set is
  empty.
* (H6) Reals `Y_0, ..., Y_(m-1)` satisfy:
  - `Y_0 >= log2 ceil(Ub)`;
  - for `1 <= t <= m-1`, `Y_t >= min C_t`, where `C_t` contains `D Y_(t-1)` and, for each `r in {2,3,4}` in use
    **with `r <= t`**, the term `Y_(t-r) + (D - 1) b_r(Y_(t-r)) - r + e_r / 2^71`, where `e_2 = 6`, `e_3 = 4`,
    `e_4 = 7`. A term with `b_r = +infinity` is `+infinity` (dropped).

**Conclusion.** `sum_{t=0}^{m-1} Y_t >= K`. Equivalently, if `sum Y_t < K`, then no cycle as in (H0)-(H2) with
these `(m, K, p)` exists.

### 3.2 Proof

**Step 1 (cycle structure).** Let `n_0` be the least element of the cycle. It is odd: if it were even, `n_0/2` would
be a smaller element. Let `q` be its predecessor in the cycle (`T(q) = n_0`). If `q` were odd, then
`n_0 = (3q+1)/2 > q`, contradicting minimality. So `q` is even, and `n_0` is a local minimum.

Start at any local minimum `u`. By section 1, the orbit makes `orun(u)` odd steps, then `l >= 1` even steps, and
reaches `nextMin(u)`, which is odd with an even predecessor, so it is again a local minimum. Every element visited
strictly between `u` and `nextMin(u)` is either odd with an odd predecessor (the 2nd to k-th elements of the
rise) or even. So none of them is a local minimum. Hence the local minima, in cycle order, are
`n_t = nextMin^t(n_0)`, `t = 0, .., m-1`, and `nextMin^m(n_0) = n_0`. The blocks `[n_t, n_(t+1))` partition one
period of the cycle. Every odd element lies in exactly one rise, so `K = sum_t k_t` with `k_t = orun(n_t)`.

**Step 2 (sum of logs).** Put `x_t = log2(n_t + 1)`. Since `2^(k_t)` divides `n_t + 1`, `k_t <= x_t`, so
`K <= sum_{t<m} x_t`.

**Step 3 (`x_0 <= Y_0`).** For every `X in (0, n_0)`, (H2) and (H3) give
`Lambda_lo - tail <= Lambda - tail < (m - m2)/X`. Let `X -> n_0` from below:
`Lambda - tail <= (m - m2)/n_0`. Now `Lambda_lo < Lambda` **strictly**. `e^Lambda = 2^p/3^K` is a rational
number other than 1 (by unique factorisation, since `K >= 1`). By Lindemann's theorem (`e^alpha` is transcendental
for algebraic `alpha != 0`), `Lambda` is not algebraic, so it is not equal to the rational `Lambda_lo`. Hence
`Lambda_lo - tail < (m - m2)/n_0`, so `m - m2 > 0`, and `n_0 < (m - m2)/(Lambda_lo - tail) = Ub`. Since `n_0` is an
integer, `n_0 <= ceil(Ub) - 1`, so `x_0 = log2(n_0 + 1) <= log2 ceil(Ub) <= Y_0`.

**Step 4 (induction).** Fix `t` with `1 <= t <= m-1`, and assume `x_j <= Y_j` for all `0 <= j < t`. It suffices
to show that `x_t <= c` for every `c in C_t`. Then `x_t <= min C_t <= Y_t`.

*1-step term.* By Lemma 20, `x_t <= delta x_(t-1)`. Since `x_(t-1) > 0` and `x_(t-1) <= Y_(t-1)`, `Y_(t-1) > 0`,
so `delta x_(t-1) <= delta Y_(t-1) <= D Y_(t-1)`.

*r-step term (2 <= r <= t).* If `b_r(Y_(t-r)) = +infinity`, there is nothing to prove. Otherwise choose
`N in G_r` with `N >= ceil(Y_(t-r))` and `g_r(N) = b_r(Y_(t-r))`. Then
`log2(n_(t-r)+1) = x_(t-r) <= Y_(t-r) <= N`, so `n_(t-r) + 1 <= 2^N`, i.e. `n_(t-r) < 2^N`. Apply the
definition of `B_r` to the odd number `n = n_(t-r)`. Its iterates are `nextMin^i(n_(t-r)) = n_(t-r+i)`, and
`t - r + i <= t - 1 <= m - 1` for `i < r`. So
`s := k_(t-r) + ... + k_(t-1) <= B_r(N) <= g_r(N) = b_r(Y_(t-r))`.
Corollary 2.3 with `n = n_(t-r)`, `m_i = n_(t-r+i)` and `m_r = n_t` gives
`x_t <= x_(t-r) + (delta - 1) s - r + c_r/((n_(t-r)+1) ln 2)`. Bound each part:
  - `x_(t-r) <= Y_(t-r)` (induction hypothesis, since `t - r < t`);
  - `(delta - 1) s <= (delta - 1) b_r(Y_(t-r)) <= (D - 1) b_r(Y_(t-r))`, using `delta - 1 > 0`, `s <= b_r`, and
    `D >= delta`. The last step uses `b_r(Y_(t-r)) >= 0`, which holds because `b_r >= s >= r > 0`;
  - `c_r/((n_(t-r)+1) ln 2) < e_r/2^71` by (H1) and section 2.

So `x_t < Y_(t-r) + (D-1) b_r(Y_(t-r)) - r + e_r/2^71`.

**Step 5.** By Steps 3-4 and induction, `x_t <= Y_t` for all `t < m`. With Step 2, `K <= sum x_t <= sum Y_t`. []

### 3.3 Notes on the statement as written in METHOD.md

1. **Windows with `t < r`.** As written, METHOD's recurrence includes the term `Y_(t-r) + ...` for every `t >= 1`.
   For `t < r` it refers to an undefined `Y_(t-r)`. The proof needs that term to be **omitted**, which is what
   "the windows never wrap" means. A wrapped window cannot be used: `x_(t-r+m) <= Y_(t-r+m)` is not yet known at
   step `t`. This is a presentation gap, not an error, provided the code omits the term. (Not checked here.)
2. **Strictness of `n_0 < Ub`.** `Y_0 >= log2 ceil(Ub)` needs `n_0 < Ub` strictly. With only `n_0 <= Ub`, the
   case `Ub = n_0`, an integer, would need `log2(Ub + 1)`. METHOD writes "by E2 with `X = n_0`". That is fine if
   E2 allows `X` equal to the least element. If E2 only allows `X` strictly below it, strictness still follows,
   because `Lambda` is transcendental and `Lambda_lo` is rational (Step 3). Either way the statement is true, but
   the condition "`Lambda_lo` rational, or `Lambda_lo < Lambda`" should be stated. The hypothesis
   `Lambda_lo > tail` is also needed for `Ub` to make sense, and METHOD does not state it.
3. **`D >= delta` and the `(D-1) b_r` term.** Replacing `delta - 1` by `D - 1` is valid because `b_r >= 0`.
   `D Y_(t-1)` is valid because `Y_(t-1) > 0`. Both are implicit in METHOD.
4. **Constants `6, 4, 7`.** Correct: `c_r/ln 2 = 2.244, 3.954, 6.234`. The 6 for r = 2 is loose. The 7 for
   r = 4 has margin 0.766.
5. **Suffix minimum.** `b_r` uses only `B_r(N) <= g_r(N)` at grid points, together with `n < 2^N` implying
   `n < 2^N'` for `N' >= N`, which is exactly the suffix minimum. No monotonicity of `B_r` is needed. Correct as
   stated.
6. **Monotonicity in `Y_0` (used by `fastchain`'s screen; not part of the theorem).** If each `Y_t` is computed
   as a monotone function (for example the min itself, rounded up) of the earlier `Y`'s, then the whole sequence
   is non-decreasing in `Y_0`. Each candidate is non-decreasing in its argument: `b_r` is non-decreasing because
   the index set `{N >= ceil(y)}` shrinks as `y` grows, and it becomes `+infinity` when the set is empty. A min of
   non-decreasing functions is non-decreasing. So a run started from an upper bound for `Y_0` gives an upper bound
   for every `Y_t`. Hence `sum Y_t` from a larger start bounds the true one, and a shape closed by the screen is
   closed. This supports METHOD section 7's claim, assuming the screen's upper bound is used only to declare
   closure (ratio < 1).
7. **B_r ranges over all odd n < 2^N.** That includes non-minima, so it is a superset of what the chain needs.
   That is valid, possibly slightly wasteful. The chain needs nothing about the descents.

## 4. Verdicts (written before the comparison)

* **Lemma 2.2, general r (in particular r = 4): PROVED** as stated (for odd `n >= 1`). Equality holds iff all
  descents are 1.
* **Corollary 2.3: PROVED** as stated: `c_r = 2((4/3)^r - 1)`, `c_4 = 350/81`, `(350/81)/ln 2 = 6.234 < 7`
  (rigorous bound `< 6.25` from `ln 2 > 56/81`), and the `r <= 13` remark is correct and sharp.
* **Chain theorem with windows of up to 4 rises: PROVED**, with three implicit hypotheses made explicit: the
  term with `t < r` is omitted; `Lambda_lo` is rational or `< Lambda` (or E2 allows `X = n_0`); and
  `Lambda_lo > tail`. Under the natural reading the statement is not false, but it is imprecise about the
  `t < r` terms.
* Lemma 20 is used as an input, and was also proved here in two lines.

## 5. Comparison with PROOFS.md section 2 and WRITEUP.md section 2.2

(This section was written after reading those two files. Sections 0-4 were already on disk.)

I read PROOFS.md section 2 (Lemma 2.1, Lemma 2.2, Corollary 2.3) and, because it is where the chain is written
out, section 3 (Theorem 3.1). I also read WRITEUP.md section 2.2, and METHOD.md sections 5 and 7-9.

**Agreement.** My proofs of Lemma 2.1, Lemma 2.2 and Corollary 2.3 follow the same route as PROOFS section 2: the
same induction, and the same geometric-sum bound giving `c_r`. PROOFS step 5 also proves Lemma 20 directly, in the
same way as here. No mathematical disagreement was found anywhere.

**Differences and gaps**, most important first:

1. **There is no written chain theorem for r = 4 apart from METHOD's.** PROOFS Theorem 3.1 is stated and proved
   only for `g2, g3`, with a three-term min. WRITEUP section 2.2 restates Lemma 2.2 and Corollary 2.3 and says
   nothing about the chain. The four-rise chain (the `r = 4` term with `+7/2^71`) exists in writing only in METHOD
   Theorem 3.1, whose proof says "three- and four-step cases are the same with Corollary 2.3". Section 3 above is,
   to my knowledge, the first full written proof of the r = 4 case. The extension is routine and correct.
2. **`c_4 = 350/81` and `(350/81)/ln 2 < 7` are not in PROOFS or WRITEUP.** PROOFS gives `c_r` in general, plus
   `c_2` and `c_3` only. WRITEUP gives the general `c_r` and the `r <= 13` remark. The r = 4 value and the
   constant 7 appear only in METHOD, and in the four-rise referee's numeric verification (METHOD section 8). They
   are proved in section 2 above with a rigorous rational bound (`< 6.25`).
3. **Windows with `t < r`.** In METHOD, PROOFS and WRITEUP the recurrence is written for all `t` with no
   restriction `t >= r`. All three cover the point only with "the windows never wrap". Presentation gap, not an
   error (section 3.3, note 1).
4. **`Lambda_lo > tail` is not stated** in METHOD or PROOFS as a hypothesis. It is needed for `Ub` to be
   positive and for the step from `Lambda < (m-m2)/n_0 + tail` to `n_0 < Ub`. Presentation gap.
5. **Strictness of `n_0 < Ub`.** PROOFS records E2 (`theorem21_two`) with "a real X <= every element". So
   `X = n_0` is allowed and the strict inequality is immediate, which settles my section 3.3 note 2 on PROOFS'
   reading of the Lean statement. I did not open the Lean file. Section 3.2 Step 3 adds a second route (`Lambda`
   is transcendental and `Lambda_lo` is rational) that needs only `X < n_0`.
6. **Passing from `delta - 1` to `D - 1`.** PROOFS step 5 derives `x_t <= Y_(t-2) + (delta-1) g2(N) - 2 + ...`,
   while the candidate in the statement has `(D-1) b2`. Two small steps are left implicit: replacing
   `delta - 1` by `D - 1` needs `g2(N) >= 0`, and the bound holds for every admissible `N`, hence for the
   minimizing one. METHOD has the same gap. It is explicit in Step 4 above.
7. **Hypothesis of Lemma 2.2.** PROOFS says "successive minima". The lemma holds for any odd `n >= 1` and its
   `nextMin` iterates (Remark ii). Harmless, since the chain applies it only to minima. PROOFS states no equality
   case. I add "equality iff all descents are 1", which shows `c_r` and (L_r) are sharp. Not needed for the result.
8. **Barina absorption for r = 4.** PROOFS records E1 as "elements >= 2^71 + 1" and uses it for `6/2^71` and
   `4/2^71`. WRITEUP section 2.2 covers r <= 13 against `2^-64`. METHOD's `7/2^71` for r = 4 is proved only in
   section 2 above. It is consistent with both.
9. **`fastchain` screen (METHOD section 7).** The validity argument is a single parenthesis in METHOD ("valid by
   monotonicity of the chain in `Y_0`"). Section 3.3 note 6 proves that monotonicity, given that each `Y_t` is a
   monotone, round-up function of the earlier values. I did not see the screen's actual bound or code, so the
   claim that its bound is a monotone upper bound remains unchecked here. METHOD says the four-rise referee proved
   the screen valid, but I have not seen that write-up.
10. WRITEUP section 2.2's statement that `chainr.py` asserts the `r <= 13` condition is about code and was not
    checked (out of scope).

## 6. Other parts of the m <= 127 argument that still have only one written proof (as far as I can see)

* **The validity of the `fastchain` screen** (item 9). Its monotonicity is now proved here. That the specific
  screen bound is a monotone upper bound, and that the acceptance rule ("worst ratio accepted only if at least the
  bound of every shape not re-run") is sound, rest on the four-rise referee's write-up. I did not locate that
  write-up.
* **Shape completeness at m = 122..127.** The mathematics (Rhin ceiling, strip, filter, monotone `lam_bound`) is
  m-independent and was proved once, in PROOFS section 3 (the referee's proof). Whether the generating session also
  wrote it is unclear. At m = 127 the computational cross-check is a count (5,291,294 inside 5,291,301), not a
  set identity.
* **Theorem R** has now been proved independently (`THEOREM-R-independent-proof.md`), and Lemma 2.2, Corollary 2.3
  and the r = 4 chain are proved here. With those, every written proof step of the four-rise chain has two
  written proofs. What remains single-sourced is computational, not proof: the B4 values, which METHOD section 8
  records as recomputed by a second implementation, and the m = 127 enumerator.
