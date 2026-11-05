# Discharging `EffMeasure` in Lean: plan (milestone 1)

Lane D90 = A. Goal: `main_statement_111_noRhin` depends only on Bařina's `2^71` hypothesis.
Status 2026-11-04: plan and paper math done, nothing in Lean yet. Scripts: `pade/`.

## 0. Summary

- **Route 1 (Padé, Rhin/Wu style) is not formalisable at a reasonable cost.**
  - The simplest Padé construction for this pair of logarithms is already borderline with *exact*
    denominators.
  - With the lcm bound Lean can actually prove (Mathlib: `θ(x) ≤ log 4 · x`), it fails by a wide
    margin.
  - Rhin's and Wu's constructions survive only by using prime-number-theorem-quality explicit bounds
    (`ψ(x) ≤ 1.04 x`, Rosser–Schoenfeld), and those are out of reach in Lean.
  - Evidence is in §2.
- **Recommended: route 2G**, Gelfond's method for two logarithms, made effective for the rationals 2 and 3.
  - Needs no prime-number estimates at all.
  - Every zero estimate is one-dimensional (a Vandermonde determinant in the exponents).
  - The Mathlib pieces exist: Siegel's lemma, Cauchy estimates, the maximum modulus principle,
    Vandermonde determinants.
  - There is a Lean template: Karatarakis–Wiedijk's Gelfond–Schneider formalisation (2026), which
    uses the same scheme and tracks its constants.
  - Our case is simpler than theirs (ℚ instead of a number field).
- **Weak target.** Gelfond's method gives `|Λ| ≥ exp(−c (log K)^5 log log K)`; we need only
  `exp(−K/2^80)`.
  - To have room, raise the `EffMeasure` threshold from `10^36` to `10^100`.
  - That costs one more δ enclosure (210 digits) and 207 Farey segments instead of 73, both checked in
    §4.
  - The slack then exceeds `10^50` in the exponent, so every constant can be chosen crudely.
- **Estimate: 4–8 weeks of Lean, about 4000–7000 lines.**
  - P(finish in 8 weeks) about 50% (range 30–70%).
  - The main risk is the "approximate Schwarz" interpolation lemma (§3, L5).
- **Fallback, route 2L:** Laurent–Mignotte–Nesterenko interpolation determinants. These avoid Siegel's
  lemma and extrapolation, but need a two-dimensional zero lemma.

## 1. The statement to prove

```
theorem effMeasure100 : ∀ p K : ℕ, 10 ^ 100 ≤ K →
    Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3|
```

The existing `EffMeasure` uses `10^36`. Two ways to connect it:

- (a) Change `EffMeasure`'s threshold to `10^100`, and extend `ceilOK` (`fareySegs` and `tailOK`) to
  `10^100` with a 210-digit enclosure `deltaLo210 / deltaHi210`. A rebuild of `EffMeasure.lean` and
  `NoRhin.lean` is cheap (about 1 minute). Recommended.
- (b) Keep `10^36` and prove the bound from `10^36`. Gelfond's loss at `10^36` (about `10^23`) is far
  above `K/2^80 ≈ 8·10^11`, so (b) would need much better constants. Rejected.

## 2. Route 1 (Padé): evidence that it does not close

The requirement for a type-II simultaneous approximation (`q log a − p_1`, `q log b − p_2` with a common
`q`) is: integerised error times denominator → 0, i.e. `α_eff = −log|E|/n − log D_n/n > 0`.

**(i) Best simple construction.** The intervals must be integer, symmetric and close to the pole:
`[−1,0]` and `[0,1]`, pole −3, so log(3/2) and log(4/3); this is the only 3-smooth choice, see
`pade/t2.py`.

| n | −log E/n | log D_n/n (exact lcm of denominators) | log d_2n/n | α_eff (exact D) |
|---|---|---|---|---|
| 10 | 2.057 | 1.508 | 1.927 | 0.550 |
| 30 | 1.924 | 1.767 | 1.918 | 0.157 |
| 60 | 1.883 | 1.833 | 1.956 | 0.050 |
| 80 | 1.886 | 1.833 | 1.959 | 0.052 |

- The error rate tends to about 1.84 and the denominator rate to about 2 (the prime number theorem),
  so even with exact arithmetic `α_eff → ≈ 0`.
- With the bound Lean can prove, `log d_2n ≤ 2n log 4 + O(√n log n)` (rate 2.77), we get
  `α_eff ≈ −0.9`.

**(ii) Other shapes.** Higher multiplicities `s^a (s−1)^b (s+1)^b` (`pade/t3.py`, 25 shapes) are all
worse: `α_eff` from −0.18 to −3.5.

**(iii) Other choices fail too.**
- Asymmetric 3-smooth intervals, such as `log(9/8)` and `log(4/3)` (pole −8), or `log(9/8)` and
  `log(32/27)`, all fail.
- Type-I three-form families `∫ t^an (1−t)^bn / ((1+t)^cn (2+t)^dn)` (`pade/scan.py`, 12 shapes) all
  have α < β.

**(iv) Rhin and Wu.** Their constructions close only through explicit prime-number-theorem-level ψ
bounds plus p-adic savings. Formalising Rosser–Schoenfeld in Lean is a research project in itself.

**Mathlib check.**
- Available: `Chebyshev.theta_le_log4_mul_x`, `psi_sub_theta_le`, `primorial_le_4_pow`.
- Missing: Padé or hypergeometric approximants, and explicit ψ bounds better than `log 4`.

**Verdict:** drop route 1.

## 3. Route 2G: Gelfond's method, effective, for log 2 and log 3

### Notation

- `μ1 = log 2`, `μ2 = log 3`, `Λ = p μ1 − K μ2`.
- Reductions (lemma L0):
  - gcd(p, K) = 1 without loss of generality: if g = gcd > 1, use `|Λ| = g|Λ'|`, and if K/g is small,
    use the trivial bound `|Λ'| ≥ 36^{−K/g}`;
  - `1.5K ≤ p ≤ 1.7K`, otherwise `|Λ| > 0.05`;
  - `Λ ≠ 0`, since `2^p ≠ 3^K`.
- Assume `|Λ| ≤ exp(−K/2^80)` and derive a contradiction.
- Exponents: `w_λ = λ1 μ1 + λ2 μ2` for `λ ∈ [0,L)^2`, so `N = L^2`. Also `u_λ = λ1 K + λ2 p ∈ ℤ`, all
  distinct (coprimality, `L < K`), and `K w_λ = μ1 u_λ − λ2 Λ`.
- Auxiliary function: `F(z) = Σ c_λ e^{w_λ z}`, entire, with `c_λ ∈ ℤ`.
- Integer approximants: `Ψ(l,m) = Σ c_λ u_λ^m 2^{λ1 l} 3^{λ2 l}`. Then
  `|K^m F^{(m)}(l) − μ1^m Ψ(l,m)| ≤ E(l,m)`, which is proportional to `|Λ|` (lemma L3).

### The steps

1. **Siegel** (Mathlib `Int.exists_ne_zero_int_vec_norm_le`). Choose `c ≠ 0` with `Ψ(l,m) = 0` for
   `l < h0`, `m < M`, and `|c| ≤ C = N (3LK)^M 6^{L h0}`, using `N ≥ 2 h0 M`.
2. **Extrapolation, by induction on h** (lemma L6): `Ψ = 0` on `[0,h) × [0,M)` implies `Ψ = 0` on
   `[0,2h) × [0,M)`, for every `h ≥ h0`.
   - `F` has approximate zeros of order M at `0..h−1`.
   - The approximate-Schwarz bound on the circle `|ζ| = 16h` and Cauchy estimates on `|z − l'| = 1/2`
     give `K^m |F^{(m)}(l')| < μ1^m / 2`.
   - `Ψ(l',m) ∈ ℤ`, so `Ψ(l',m) = 0`.
   - The step closes once `2.015 h M > 28.7 L h + M(log K + log M + 1.1) + log 2NC`, true for
     `h ≥ h0` when `M = 20L`.
3. **Final step.** With `Ψ = 0` on `[0,H) × [0,M)`, approximate Schwarz on `|ζ| = 20H` gives
   `|F| ≤ exp(log NC − 23 L H)` on `|z| ≤ 1`.
   - Cauchy then gives `|F^{(m)}(0)| ≤ m! |F|_1` for `m < N`.
   - But `(F^{(m)}(0))_{m<N} = V c` with `V = (w_λ^m)` a Vandermonde matrix:
     - `|det V| ≥ (36^{−L})^{N(N−1)/2}`, from the separation lemma L8:
       `|a μ1 + b μ2| ≥ 36^{−L}` for small `(a, b) ≠ 0`, because `2^a 3^b ≠ 1`;
     - the cofactors are bounded by `Matrix.det_le`.
   - So `1 ≤ ‖c‖ ≤ ‖V^{−1}‖ ‖Vc‖ < 1` once `H > N^2 (1.8 L + log 1.8L)/(23L) + …`.
4. **Loss.** All approximation errors, amplified by the interpolation constants, must stay below 1.
   This needs `log(1/|Λ|) > LOSS`, with `LOSS ≈ 1.8 L H + H M log(40H) + 1.8 L N^2 + …`.

### Parameter check (`pade/gelfond_params.py`)

Every margin is positive.

| K | L | M | h0 | H | LOSS | K/2^80 |
|---|---|---|---|---|---|---|
| 1e60 | 24 482 | 489 640 | 612 | 2.8e16 | 5.9e23 | 8.3e35 |
| 1e100 | 39 522 | 790 440 | 988 | 1.9e17 | 6.7e24 | 8.3e75 |
| 1e200 | 77 082 | 1.54e6 | 1 927 | 2.7e18 | 2.0e26 | 8.3e175 |
| 1e1000 | 376 922 | 7.5e6 | 9 423 | 1.6e21 | 6.4e29 | ≫ |

- LOSS grows like `(log K)^5 log log K`, and K/2^80 grows like K. From `10^60` up the margin only
  increases, which is easy to prove monotonically in Lean once the parameters are functions of
  `⌈log K⌉`.
- At `10^36` the loss (about `10^23`) is larger than K/2^80 (about `10^12`), hence the threshold change
  in §1.
- These are design numbers from analytic upper bounds; the Lean proof needs only inequalities of the
  same shape.

## 4. Threshold `10^100`: finite part re-checked

- `pade/segs_hi.py`, run with a mock 210-digit enclosure, finds 207 consecutive-convergent Farey
  segments from `1/1` to `b + d ≈ 6.8·10^100`.
- All m = 1..111 close, with minimum gap `c/d − δ⁺ = 2.7·10^{−203}`, well above the enclosure width
  `10^{−210}`.
- In Lean this needs `LogTwoThreeBounds210.lean` (logSum at 1/2 with about 715 terms and at 1/3 with
  about 452 terms, `decide +kernel`) and new constants in `segOK` and `tailOK`.
- About one day of work, with kernel time of minutes (estimated).

## 5. Lean decomposition (milestone 2 = this skeleton with `sorry`s)

| id | lemma | content | Mathlib support | est. lines |
|---|---|---|---|---|
| L0 | reductions | gcd, the range of p/K, `Λ ≠ 0` | elementary | 150 |
| L1 | `auxF`, derivatives | `F^{(m)}(z) = Σ c w^m e^{wz}`, entire, growth `|F(z)| ≤ ‖c‖₁ e^{w_max|z|}` | `iteratedDeriv`, `Complex.exp` | 250 |
| L2 | Siegel application | the matrix `(u^m 2^{λ1 l} 3^{λ2 l})`, bound on `‖c‖` | `Int.exists_ne_zero_int_vec_norm_le` | 250 |
| L3 | approximation | `|K^m F^{(m)}(l) − μ1^m Ψ(l,m)| ≤ E` | mean value, `pow_sub_pow` | 200 |
| L4 | Hermite interpolant | polynomial `P` of degree < hM matching data at the nodes `0..h−1`, `|P| ≤ ε B(h,M,R)` on `|z| ≤ R` | explicit basis via `Polynomial` and divided differences | 900 (risk) |
| L5 | approximate Schwarz | `(F − P)/Q` entire (removable singularities); maximum modulus gives `|F − P| ≤ (r/R)^{hM}`-type bound | `AnalyticAt.order`, `dslope`, `Complex.norm_le_of_forall_mem_frontier_norm_le`; Karatarakis' gluing lemmas | 900 (risk) |
| L6 | extrapolation step and induction | combines L1, L3–L5 with Cauchy estimates (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) and integrality | Mathlib | 500 |
| L7 | Vandermonde final step | `‖V^{−1}‖` bound via adjugate, `Matrix.det_le` | `Matrix.det_vandermonde` | 400 |
| L8 | separation | `|a log 2 + b log 3| ≥ 36^{−L}` | elementary | 100 |
| L9 | parameters | the real inequalities for `L, M, h0, H` as functions of `⌈log K⌉`, monotone from `10^100` | `nlinarith`, logs | 800 |
| L10 | assembly | `effMeasure100`, then the new `EffMeasure` and `main_statement_111` with only `hX` | — | 150 |
| L11 | threshold 10^100 | 210-digit enclosure, regenerated `fareySegs`, `tailOK` at `10^100` | existing pattern | 200 + data |

- Total about 5000 lines, plus data.
- L4 and L5 are about 40% of the risk. Two ways to lower it:
  - prove the residue-free form "`F − P` has a zero of order M at each node, so `(F − P)/Q` is entire";
  - bound `P` through an explicit Lagrange–Hermite basis on integer nodes, with crude factorial bounds
    (the slack allows `exp(H M log(40H))`).

## 6. Milestones and reporting

1. This plan, reported now.
2. Skeleton: `Collatz/Gelfond/*.lean`, with the statements of L0–L11 and `sorry` bodies, building on
   rc3. I will report an honest count of the `sorry`s.
3. Discharge the `sorry`s in this order: L8, L0, L1, L3, L2, L7, L9, L4, L5, L6, L11, L10, reporting
   at each module. L11 can start in parallel since it is independent.

- **Build rules:** broker lease, `PY=/c/Python314/python`, at most 2 threads while Lee is present
  (1 under GAMING), honest `--eta-minutes`, no `native_decide`.

## 7. Full-tree trust replay (separate)

- `replay_chunked.sh` runs leanchecker on 20-module chunks, resumable through
  `logs/replay_done.txt`. It is meant to run detached and preemptible on one thread when the machine
  is idle.
- **Not started yet:** at 2026-11-04 about 7 pm EST the broker showed commit charge at 99% (DANGER), so
  nothing large is started now.
