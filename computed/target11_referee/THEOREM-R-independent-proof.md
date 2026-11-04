# Theorem R: an independent proof

Written 2026-11-03 by an AI referee (Claude). I wrote this from the statement in `METHOD.md` section 3 and the
definitions in sections 1-2, before reading the existing proof in `computed/target7c_proofs/PROOFS.md`, `b4join.py`
or `refb4.py`. **Disclosure:** the read of `METHOD.md` lines 1-160 that gave me the statement also showed me the
written proof of Theorem 1 (the r = 3 case, lines 127-148) and the one-sentence sketch after Theorem R
(lines 156-158). So this proof is clean-room with respect to `PROOFS.md` and the code, but not with respect to
that text. The route below is my own: a one-line recursion for `nu`, and one induction on the number of blocks.
Section 5 compares it with the existing proof.

**Verdict: PROVED, as stated, for every r >= 1, with the implicit hypothesis N >= 1 made explicit.** (The statement
also holds for N = 0 if you read "max of the empty set" the same way on both sides.)

---

## 0. Definitions used

* `T : Z_2 -> Z_2`, `T(x) = x/2` if `x` is even, `(3x+1)/2` if `x` is odd. It restricts to `Z_{>=0} -> Z_{>=0}`.
* The *parity vector* of `x in Z_2` is the sequence `(T^j(x) mod 2)_{j >= 0}`.
* **Fact P** (Terras). For each `L >= 0`, `x mod 2^L` determines the first `L` parities of `x`, and
  `Z/2^L -> {0,1}^L` is a bijection. (Taken as known. It is [Lean] in this repository and is classical.)
* **Blocks.** For an odd integer `n >= 1` write `n + 1 = 2^k a` with `a` odd, so `k = orun(n) >= 1`. Put
  `l = v_2(3^k a - 1)`. This is finite and `>= 1` because `3^k a - 1 >= 2` is even. Put
  `nextMin(n) = (3^k a - 1)/2^l`, an odd integer `>= 1`. The pair `(k, l)` is the *block* of `n`.
* For odd `n >= 1`, put `m_0 = n` and `m_{i+1} = nextMin(m_i)`. Let `(k_i, l_i)` be the block of `m_i`. Then

      B_r(N) = max { k_0 + ... + k_{r-1} : n odd, 1 <= n < 2^N }.

* `u_k = (2/3)^k in Z_2`. This is well defined because 3 is a unit of `Z_2`, and `v_2(u_k) = k`.
* For `x in Z_2 \ {0, 1, ..., 2^N - 1}`, `z_N(x)` is the least `i >= N` such that bit `i` of `x` is 1. Such an `i`
  exists exactly when `x` is not an integer in `[0, 2^N)`: if bits `N, N+1, ...` all vanish, then
  `x = x mod 2^N in [0, 2^N)`.
* For `q >= 0` and `sigma = (k_0, l_0, ..., k_{q-1}, l_{q-1}) in Z_{>=1}^{2q}`, put

      K_i = k_0 + ... + k_i,   Lambda_i = l_0 + ... + l_{i-1}   (Lambda_0 = 0),
      lambda(sigma) = Lambda_q,   P(sigma) = K_{q-1} + lambda(sigma)   (P = 0 when q = 0),
      nu(sigma) = -1 + sum_{i=0}^{q-1} 2^{Lambda_i} u_{K_i} (1 - 2^{l_i})   in Z_2.

  Theorem R takes `q = r - 1`: `nu_r(sigma) = nu(sigma)` and `P = K_{r-2} + lambda`. Also write
  `w(sigma) = 1^{k_0} 0^{l_0} ... 1^{k_{q-1}} 0^{l_{q-1}}`, a word of length `P(sigma)`.

**Theorem R.** Let `r >= 1` and `N >= 1`. For every `sigma in Z_{>=1}^{2(r-1)}`:

(a) the parity vector of `nu(sigma)` is `w(sigma) 1^infinity`;

(b) `nu(sigma)` is not an integer in `[0, 2^N)`, so `z_N(nu(sigma))` is defined and finite;

(c) the set `V = { z_N(nu(sigma)) - lambda(sigma) : sigma in Z_{>=1}^{2(r-1)}, z_N(nu(sigma)) > P(sigma) }` is
nonempty and finite, and `max V = B_r(N)`.

Moreover, `z_N(nu(sigma)) > P(sigma)` holds iff some odd `n in [1, 2^N)` has first `r - 1` blocks equal to `sigma`.
For such `sigma`, `z_N(nu(sigma)) - lambda(sigma)` is the largest value of `k_0 + ... + k_{r-1}` among those `n`.

(The case `r = 1` is included: `sigma` is empty, `nu = -1`, `z_N(-1) = N`, and the theorem says `B_1(N) = N`, which
`n = 2^N - 1` attains.)

---

## 1. A recursion for nu

**Lemma 1.** Let `q >= 1`, `sigma = (k_0, l_0) . sigma'`, where `sigma' = (k_1, l_1, ..., k_{q-1}, l_{q-1})`. Then

    nu(sigma) + 1 = u_{k_0} * (1 + 2^{l_0} nu(sigma')).

*Proof.* Write `K'_j, Lambda'_j` for the partial sums of `sigma'`, indexed from `j = 0`. For `i >= 1`,
`K_i = k_0 + K'_{i-1}` and `Lambda_i = l_0 + Lambda'_{i-1}`. So `u_{K_i} = u_{k_0} u_{K'_{i-1}}` and
`2^{Lambda_i} = 2^{l_0} 2^{Lambda'_{i-1}}`. Split off the `i = 0` term:

    nu(sigma) + 1 = u_{k_0}(1 - 2^{l_0}) + u_{k_0} 2^{l_0} sum_{j=0}^{q-2} 2^{Lambda'_j} u_{K'_j}(1 - 2^{l'_j})
                  = u_{k_0}(1 - 2^{l_0}) + u_{k_0} 2^{l_0} (nu(sigma') + 1)
                  = u_{k_0} (1 + 2^{l_0} nu(sigma')).                                               []

## 2. The rise lemma in Z_2

**Lemma 2.** Let `x in Z_2`, `k >= 0`, and `x + 1 = 2^k a` with `a in Z_2`. Then for `0 <= j <= k`,
`T^j(x) + 1 = 3^j 2^{k-j} a`. In particular `x, T(x), ..., T^{k-1}(x)` are odd and `T^k(x) = 3^k a - 1`.

*Proof.* Induction on `j`. The case `j = 0` is the hypothesis. Suppose `j < k` and the claim holds at `j`. Then
`T^j(x) + 1` is divisible by `2^{k-j}`, with `k - j >= 1`, so `T^j(x)` is odd and
`T^{j+1}(x) + 1 = (3 T^j(x) + 1)/2 + 1 = 3 (T^j(x) + 1)/2 = 3^{j+1} 2^{k-j-1} a`.                    []

## 3. Proof of (a) and (b)

**Proof of (a).** Induction on `q = r - 1 >= 0`; write `nu` for `nu(sigma)`.

*`q = 0`:* `nu = -1`, which is odd, and `T(-1) = (-3 + 1)/2 = -1`. So the parity vector is `1^infinity`.

*`q - 1 -> q`:* write `sigma = (k_0, l_0) . sigma'` and `nu' = nu(sigma')`. By the induction hypothesis the parity
vector of `nu'` is `w(sigma') 1^infinity`. It starts with 1 (either `k_1 >= 1`, or `sigma'` is empty), so `nu'` is
odd. By Lemma 1, `nu + 1 = 2^{k_0} a` with `a = 3^{-k_0}(1 + 2^{l_0} nu') in Z_2`. Lemma 2 now shows that
`nu, ..., T^{k_0 - 1}(nu)` are odd and

    T^{k_0}(nu) = 3^{k_0} a - 1 = 2^{l_0} nu'.

Because `nu'` is odd and `l_0 >= 1`, `T^{k_0 + j}(nu) = 2^{l_0 - j} nu'` is even for `0 <= j < l_0`, and
`T^{k_0 + l_0}(nu) = nu'`. So the parity vector of `nu` is `1^{k_0} 0^{l_0}` followed by that of `nu'`, which is
`w(sigma) 1^infinity`.                                                                                       []

**Proof of (b).** Suppose `nu = n in Z_{>=0}`. `T` maps `Z_{>=0}` into itself. By (a), `T^j(n)` is odd for every
`j >= P`. Applying Lemma 2 to `y = T^P(n)` with `y + 1 = 2^k a'`, `a'` odd (note `y + 1 >= 1`): if `k` is finite, then
`T^k(y) = 3^k a' - 1` is even, a contradiction. So `y + 1 = 0`, which is impossible for `y >= 0`. Hence `nu` is not a
non-negative integer, and in particular not one in `[0, 2^N)`.                                               []

## 4. Proof of (c)

Fix `sigma` with `q = r - 1` blocks, and write `nu = nu(sigma)`, `P = P(sigma)`, `z = z_N(nu)`.

**Lemma 3 (parity description of runs).** Let `n >= 1` be odd and `j >= 1`. The following are equivalent:
(i) the first `r - 1` blocks of `n` are `sigma` and `k_{r-1}(n) >= j`;
(ii) the first `P + j` parities of `n` are `w(sigma) 1^j`.

*Proof.* For odd `n >= 1`, Lemma 2 (applied to `n + 1 = 2^k a`, `a` odd) and the definition of `l` show that the
parity vector of `n` is `1^{k} 0^{l}` followed by the parity vector of `nextMin(n)`. So it is the infinite
concatenation `1^{k_0(n)} 0^{l_0(n)} 1^{k_1(n)} 0^{l_1(n)} ...`, where every exponent is finite and `>= 1`. These are
exactly the maximal runs of the sequence. (i) => (ii) is immediate. For (ii) => (i): every run of `w(sigma) 1^j`
except the last ends where the next, opposite, symbol begins inside the word. So the runs of `n`'s parity vector up
to and including `0^{l_{r-2}}` are exactly `k_0, l_0, ..., l_{r-2}`, and the next run of 1s has length `>= j`.  []

**Lemma 4 (the residue class).** Let `L >= 1`. The class `C = nu + 2^L Z_2` consists of odd elements, and it contains
an integer in `[1, 2^N)` iff `L <= z`.

*Proof.* The first parity of `nu` is 1. For `r >= 2` this is because `k_0 >= 1`; for `r = 1`, `nu = -1`. Every element
of `C` agrees with `nu` mod 2, so all are odd. Let `rho = nu mod 2^L in [0, 2^L)`, the least non-negative element
of `C`. It is odd, so `rho >= 1`, and `C ∩ Z_{>=0} = rho + 2^L Z_{>=0}`.
If `L <= N`: `rho < 2^L <= 2^N` lies in `C ∩ [1, 2^N)`, and `z >= N >= L`.
If `L > N`: `C` meets `[1, 2^N)` iff `rho < 2^N`. That holds iff bits `N, ..., L-1` of `rho`, equivalently of `nu`,
are all 0, and that holds iff `z >= L`.                                                                         []

**Corollary 5.** Let `j >= 1`. An odd `n in [1, 2^N)` with first `r - 1` blocks `sigma` and `k_{r-1}(n) >= j` exists
iff `P + j <= z`.

*Proof.* By Lemma 3 these `n` are the odd `n in [1, 2^N)` whose first `P + j` parities are `w(sigma) 1^j`. By (a),
`nu` has this prefix. By Fact P, the elements of `Z_2` with this prefix form exactly the class
`nu + 2^{P+j} Z_2`. Every element of that class is odd, by Lemma 4. Lemma 4 with `L = P + j` finishes the proof. []

**Proof of (c).** Let `F` be the set of `sigma` such that some odd `n in [1, 2^N)` has first `r - 1` blocks `sigma`.
Every odd `n` has `k_{r-1}(n) >= 1`. So by Corollary 5 with `j = 1`, `sigma in F` iff `z > P`, which is the claimed
characterisation of feasibility. For `sigma in F`, Corollary 5 shows that the largest `k_{r-1}` among those `n` is
`j*(sigma) = z - P >= 1`: it is attained at `j = z - P`, and `j = z - P + 1` is impossible. So the best total over
those `n` is

    K_{r-2} + j*(sigma) = K_{r-2} + z - K_{r-2} - lambda = z_N(nu(sigma)) - lambda(sigma).

So `V = { best total for sigma : sigma in F }`. `F` is finite and nonempty: each `sigma in F` is the block prefix of
one of the finitely many odd `n < 2^N`, and `n = 1` exists because `N >= 1`. Every element of `V` is the total
`k_0 + ... + k_{r-1}` of some odd `n < 2^N`, so `max V <= B_r(N)`. Conversely, if `n` attains `B_r(N)` and `sigma` is
its block prefix, then `sigma in F` and the element of `V` for `sigma` is `>= B_r(N)`. Hence `max V = B_r(N)`, and
the maximum is attained.                                                                                       []

---

## 5. Comparison with the existing proof (written after sections 0-4)

Sources read for this section:
* `METHOD.md` section 3, lines 113-158;
* `computed/target7c_proofs/PROOFS.md` section 1 (Theorem 1 and Lemmas 1.1-1.3; it has no general-r Theorem R);
* the only written general-r proof, `collatz-loop/research/target10_rrise/WRITEUP.md` section 2.1 (development
  repository; `b4join.py` cites it as "WRITEUP.md section 2"), which METHOD.md abbreviates in one line;
* the docstrings of `b4join.py` and `refb4.py`.

**Same core.** The existing proof uses the same factorisation, `nu + 1 = u_{k_0} c` with
`c - 1 = 2^{l_0} nu_{r-1}(sigma')`. That is my Lemma 1, and it gives the same induction on the number of blocks.
It then finishes "word for word" as Lemmas 1.2-1.3 of target7c. The two proofs reach the same statement, and I found
**no mathematical error**. The differences are all completeness or rigour points:

1. **Range of r and N.** The statement is for `r >= 2`, but the induction starts at `r = 1` (`nu = -1`). It never
   states that `B_1(N) = N` fits the same formula, though that is harmless. `N >= 1` is never stated. My (c) makes
   both explicit.
2. **Oddness of `nu_{r-1}(sigma')`** is asserted ("the factor ... is odd") without saying why. It follows from the
   induction hypothesis, since the parity vector starts with 1. My proof says this. The existing proof also shows
   `c` is odd ("the bracket is in 2Z_2"), which is equivalent: the bracket is `nu(sigma') + 1`.
3. **"The n with runs sigma and k_{r-1} >= j form exactly the class nu mod 2^{P+j}."** As written this is
   imprecise. The class is a set of 2-adic integers; what is true is that the *odd positive integers* in the class
   are exactly those `n`. More substantively, the equivalence between "runs = sigma and `k_{r-1} >= j`" and "parity
   prefix = `w 1^j`" is left to target7c Lemma 1.2. That lemma justifies it only by "the trailing `1^j` closes the
   run". It never states the fact this needs: the parity vector of a positive odd integer is the concatenation of
   its blocks `1^{k_i} 0^{l_i}`, with every exponent finite and `>= 1`. My Lemma 3 proves it, using Lemma 2 for
   integers.
4. **Finiteness of `z_N(nu)`** (target7c Lemma 1.3, inherited). The argument given is "nu would be a positive integer
   whose parity vector ends in 1^infinity, so v_2(nu+1) = infinity". The last step is wrong as written:
   `v_2(nu + 1) = k_0` is finite. The infinite valuation is that of `T^P(nu) + 1`. My (b) applies the argument to
   `y = T^P(nu)` and uses the fact that `T` maps non-negative integers to non-negative integers. This is a slip,
   not a gap in the theorem. (It also says "positive" where "non-negative" is needed; `nu = 0` is excluded anyway,
   because `nu` is odd.)
5. **Existence of the maximum and finiteness of the feasible set** are proved in target7c only for r = 3, and
   carried to general r by "word for word". Mine proves them for general r: `F` is finite because each
   `sigma in F` is a block prefix of some odd `n < 2^N`.
6. **Odd elements of the class.** target7c Lemma 1.3 uses the fact that the least representative is odd, and hence
   `>= 1`. My Lemma 4 says the whole class is odd because the first parity of `nu` is 1. This is the same point,
   stated explicitly.
7. **Route to "exactly k_0 odd steps".** The existing proof first shows `a = 3^{-k_0} c` is a unit, then uses
   "as in the integer case". Mine uses a 2-adic Lemma 2, which does not need `a` odd, and gets the end of the run
   from `T^{k_0}(nu) = 2^{l_0} nu'` being even.

**Which direction the code uses.** Neither `b4join.py` nor `refb4.py` evaluates the max formula as an exact value.
Both use only the necessary direction: an odd `n < 2^N` with value `>= V` satisfies
`n ≡ nu(sigma(n)) (mod 2^{v + lambda})`, so certain bits of `nu` vanish and `n = nu mod 2^N`. Every candidate is then
re-simulated literally. Soundness of the tables (no value understated) needs only (a), Lemma 3 (i)=>(ii), and
Fact P. The sufficiency half (Lemma 4 with `L <= z`, and attainment) only makes the method complete, not sound.
These are exactly the parts of my proof that are fully elementary.

## 6. What this proof does not cover in the r = 4 use for m <= 127

Theorem R is a statement about each `sigma`. The `B4` table also depends on the following, none of which is part
of Theorem R or of this proof:

1. **Finite search ranges.** The search must cover every `sigma` that can occur for an odd `n < 2^N`.
   `b4join.py` uses `k_0 <= N` and `K_1 <= ceil(2.585 N) + 2`. (I checked quickly: `k_1 <= log2(n_1 + 1)
   <= N + (delta - 1) k_0`, so `K_1 <= (1 + delta) N < 2.585 N`. This holds.) It also uses three kinds of group
   items for large `l_1`, `K_2`, `l_2`, plus "region C" (`k_0 + l_0 >= N`). `refb4.py` uses its own partition into
   classes. Those partitions being exhaustive is a separate lemma about each code. It is argued in their
   docstrings, not here.
2. **Window arithmetic.** The claim is that bits `[N, N+R)` of `nu` equal `(sum of ±w_j + e) mod 2^R` with
   `e in [-3, 3]`, together with the 64-bit truncation of windows. This is finite-precision bookkeeping and is not
   covered here.
3. **Stopping rule.** "Exact once best >= N + t - 1" (b4join) or threshold `V` (refb4): if the threshold is too
   high, the max is not found and the run must be repeated. That logic is in the drivers.
4. **The four-step chain inequality** (Lemma 2.2 at r = 4, `c_4 = 350/81`) and the **chain theorem with r = 4
   windows** (Theorem 3.1). These are separate results, [proved on paper] only, and not addressed here.
5. **Grid use.** The suffix-minimum lookup `b_4(y)` needs only `B_4(N) <= g_4(N)` at grid points, and that is what
   Theorem R plus correct code gives. No monotonicity of `B_4` is needed, so none is proved here.

Only item 4 is mathematics of the same kind as Theorem R. Items 1-3 are correctness of the implementations, which
the two independent codes and the brute-force agreement for `N <= 22` address empirically.

## Appendix: numerical sanity check

A throwaway script (not committed; under 60 s) checked, for r = 2 and N <= 11, r = 3 and N <= 7, and r = 4 and
N <= 4:
(1) the first `P + 20` parities of `nu(sigma)`, computed mod `2^(P+N+80)`, are `w(sigma) 1^20`;
(2) inside a box of `sigma` one wider than every feasible `sigma` found by brute force, `{sigma : z_N(nu) > P}` is
exactly the set of block prefixes of odd `n < 2^N`;
(3) `max V` equals the brute-force `B_r(N)`.
All checks passed.
