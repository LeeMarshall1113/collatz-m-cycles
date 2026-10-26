# collatz-m-cycles

**Every nontrivial positive Collatz cycle has at least 112 local minima** (no m-cycle with m <= 111), proved in
Lean 4 and kernel-checked, assuming two published inputs (stated precisely below). A further extension to
m <= 127 is **computed and independently re-computed, but not formally verified**.

## The theorem

```lean
-- Collatz/MCycle111.lean
theorem Collatz.no_111_cycle_2_71
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1)
    (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 112 ≤ numLocalMin x p
```

In words: if every `n` with `0 < n <= 2^71` reaches 1 under the Collatz map, and `RhinBound` holds, then every
positive cycle of `T` other than `1 -> 2 -> 1` has at least 112 local minima.

Definitions the statement depends on (in `Collatz/Defs.lean`, `Collatz/Statements.lean`,
`Collatz/HercherRhin.lean`; `scripts/Statement.lean` re-states them unfolded and checks them with `rfl`):

```lean
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2          -- the shortcut Collatz map
def Reaches (f : ℕ → ℕ) (n m : ℕ) : Prop := ∃ k, f^[k] n = m
def numLocalMin (x p : ℕ) : ℕ :=                                              -- odd elements whose cyclic
  ((range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0)).card  -- predecessor is even
def RhinBound : Prop :=                                                       -- Simons-de Weger Lemma 12
  ∀ x p : ℕ, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 1 ≤ oddCount T x p →
    Real.exp (-(133 / 10 * (46057 / 100000 + Real.log (oddCount T x p)))) <
      (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3
```

### Hypotheses (these are parameters of the theorem, not axioms)

* **`hX`**: every `0 < n <= 2^71` reaches 1. This is a published computation, D. Bařina, *J. Supercomput.* 81
  (2025), art. 810 (verified to just above 2^71; `n = 2^71` is a power of 2). It is **not** verified here.
* **`RhinBound`**: Rhin's effective irrationality measure for `log 3 / log 2`, in the form used for cycles by
  J. Simons and B. de Weger, *Acta Arith.* 117 (2005), Lemma 12 (G. Rhin, *Progr. Math.* 71 (1987), 155-164). It is
  a transcendence-theory input that is not in Mathlib, so it is carried as a hypothesis.
* `p` need not be the least period; taking `p` minimal gives the count for the cycle itself, and a multiple of the
  period multiplies the count, so the theorem covers the minimal case.
* Beyond `hX` and `RhinBound`, the proof uses only `propext`, `Classical.choice`, `Quot.sound` (see below). The
  sources contain no `sorry`, no `native_decide` and no user `axiom`.

## What is verified, and what is not

| Range | Status | Where |
|---|---|---|
| m <= 91 | Lean, kernel-checked (Hercher's theorem, formalised by Alick) | `Collatz/Hercher*.lean` |
| m <= 101 | Lean, kernel-checked (Alick) | `Collatz.no_101_cycle_2_71` |
| **m <= 111** | **Lean, kernel-checked (this repository)** | `Collatz.no_111_cycle_2_71`, `main_statement_111` |
| **m <= 127** | **Computed (exact rational arithmetic), re-computed by independent referee code; NOT formally verified** | `computed/`, `METHOD.md` section 7 |

* **Lean-verified (m <= 111).** Kernel-checked from `hX` and `RhinBound`. `#print axioms main_statement_111`
  gives `[propext, Classical.choice, Quot.sound]`, and the audit of all 64,104 declarations in the `Collatz`
  namespace finds nothing else (`AXIOM_AUDIT.txt`). The numerical facts the chain argument needs (rise bounds, shape
  lists, per-shape certificates) are re-checked by the kernel; the Python generators are not trusted.
* **Computed and refereed, not verified (m <= 127).** The same method with an added *four-rise* bound closes every
  surviving cycle shape for m <= 127 (5,291,301 candidate shapes at m = 127, no failures; the tightest case has
  ratio 0.9963 < 1). The Python is exact (rational arithmetic, upward rounding, every witness re-simulated). The
  three-rise part (m <= 121) was re-computed by two independent AI referee sessions plus a third bulk check; the
  four-rise part (m = 122 ... 127) by one independent referee session with its own B4 code (`METHOD.md` section 8).
  It is **not** in Lean: the rise bounds needed for m <= 127 would take more than 10^6 kernel-hours with the present
  approach. Treat m <= 127 as a strongly cross-checked computation, not as a theorem. The margin at m = 127 is
  0.37%, and the argument is sensitive to the exactness of the rise-bound tables (`METHOD.md` section 9).
* **Hypotheses `hX` and `RhinBound` apply to both.**

## Check it

Requirements: [elan](https://github.com/leanprover/elan) (toolchain `leanprover/lean4:v4.35.0-rc3`, pinned in
`lean-toolchain`), git, and a machine with **at least 16 GB of RAM or pagefile** (see "Cost" below).

```sh
lake exe cache get          # prebuilt Mathlib
lake build Collatz && lake env lean scripts/Statement.lean
```

Expected output of the second command (`scripts/Statement.lean`):

```
'main_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_102' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_103' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_105' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_106' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_107' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_108' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_109' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_110' depends on axioms: [propext, Classical.choice, Quot.sound]
'main_statement_111' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Optional full audit of every `Collatz` declaration (expected: `audited 37298 declarations: only propext,
Classical.choice, Quot.sound`):

```sh
lake env lean scripts/AxiomAudit.lean
```

### Build one module at a time

`lake build Collatz` runs as many Lean processes in parallel as there are cores, and several of the generated
modules are large. **On a machine with limited RAM build serially**, one module (one Lean process) at a time, in
dependency order:

```sh
python scripts/build_serial.py            # builds every module reachable from Collatz.lean, one at a time
python scripts/build_serial.py --list     # just print the order
```

### Cost (approximate, from our own incremental runs; not a clean from-scratch measurement)

* **Time.** About 1,200 generated modules (shape walks, per-shape certificates, rise-bound checks). Our incremental
  builds on one Lean process: m <= 108 about 40 minutes, m = 109 about 2 hours, m = 110 about 6 hours and m = 111 about 15 hours on top, so
  **roughly 9-10 hours** for a serial from-scratch build after the Mathlib cache download. Alick's original m <= 101
  build took about 18 minutes on a GitHub runner.
* **Peak RAM per Lean process.** Working set below about 4 GB for the logged m <= 110 modules (most 1.7-2.6 GB; the
  Mathlib import alone is about 1.6 GB); commit charge up to about 5-6 GB for some. Alick's `MCycle101Data` and
  `MCycle102Data` were measured at about 15 GB commit on our machine (his README says 2 GB; we have not re-measured
  in this clone). Do not run many in parallel on a small machine: on our shared machine memory was exhausted
  repeatedly.
* **CI.** `.github/workflows/lean.yml` is manual-only (`workflow_dispatch`); the m <= 111 build does not fit the
  original 90-minute timeout.

## Prior work

* **C. Hercher**, *There are no Collatz m-cycles with m <= 91*, J. Integer Seq. 26 (2023), Art. 23.3.5, with the
  corrigendum of June 2026 (the error repaired there was found by Xinjun Wang). m <= 91.
* **J. Simons, B. de Weger**, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith.
  117 (2005): the m-cycle framework and the use of Rhin's measure.
* **Justin Alick**, [collatz-m-cycles-101-lean](https://github.com/justinalick/collatz-m-cycles-101-lean)
  (Apache-2.0): a Lean 4 formalisation of Hercher's theorem and a two-rise extension, m <= 101.
* **D. Palmqvist**, [dpalmqvist/kollatz](https://github.com/dpalmqvist/kollatz), `notes/mcycles_extension.md`:
  claims m <= 104 (Lean, two-rise method with more grid points, replayed with `leanchecker` and `nanoda`). The best
  public claim we found before this work.

We searched GitHub and the web on 2026-10-24 and found no public claim above m <= 104. That search is not exhaustive.

## What is Alick's and what is new

**Alick's (commit `d189594`, kept in this repository's history unmodified; Apache-2.0).** The whole Lean base:
the Collatz map and cycle identities (`Defs`, `Statements`, `Terras`, `Cycles`, `ParityVector`, ...); the
formalisation of Hercher's m <= 91 theorem (`Hercher*.lean`, `FareyCertificate`, `LogTwoThreeBounds`); `RhinBound`
as a hypothesis; the **two-rise bound** (`TwoRiseCheck.lean`, the `MCycleTwoRiseLo/Hi*.lean` and `MCycleGridLo/Hi.lean`
modules for his grid) and the one- and two-step lemmas (`MCycleSteps.lean`); the **chain argument**
(`MCycleChain.lean`) and the Farey **walk** that lists surviving cycle shapes (`MCycleWalk.lean`); the m = 92 ... 101
certificate modules and their generators (`research/scripts/mcycle101_certgen`, `hercher_*.py`);
`scripts/AxiomAudit.lean`, `scripts/Statement.lean` (up to m <= 101) and the CI workflow. The method of
"two-rise bound + chain of minima" is his. None of his Lean files is modified here except the root `Collatz.lean`
(extra imports); the CI workflow and the `Statement.lean` header are edited in our release-preparation commit.

**New in this repository (generated by Claude under Lee Marshall's direction).**

* **Three-rise bound.** Theorem 1 (a 2-adic formula for the maximal total length B3(N) of three consecutive rises),
  Lemma 3S (the three-step chain inequality), the B3 grid, and the Lean checker `AllTriples` with its soundness
  proof: `ThreeRiseCheck.lean`, `MCycleSteps3.lean`, `MCycleChain3.lean`, `ThreeRiseSplit.lean`,
  `MCycleThreeRise*.lean`, `MCycleGrid3_*.lean`. We found no prior art for the three-rise bound.
* **Linear-time two-rise checker** (`TwoRiseCheck2.lean`, `TwoRiseCheck3.lean`) and the large new two-rise grid
  points (`TwoRise2_*.lean`, up to N = 647,476), replacing a checker that stalled on large N.
* **Extension to m = 102 ... 110**: shape walks, per-shape certificates and data modules
  (`MCycle102* ... MCycle110*`, `WalkSplit.lean`, `MCycleGrid102 ... 110`), their generators
  (`research/scripts/mcycle{103_split,105,107,109}`, `research/scripts/lean127/gen*.py`) and the theorems `no_102_cycle_2_71 ...
  no_110_cycle_2_71`.
* **Four-rise extension to m <= 127** (computed, not in Lean): `METHOD.md` section 7 and `computed/`.
* **Extension to m = 111**: `LogTwoThreeBounds80.lean` and `MCycleChain3D.lean` (a 10^-80 enclosure of log2 3, needed
  from m = 111 for one shape), the three-rise grid `grid3_111` (B3 at 498 and 522) and `MCycle111*`. `BenchKernel.lean`
  is a benchmark, not used by any theorem.
* `METHOD.md`, `computed/`, `NOTICE`, `AXIOM_AUDIT.txt`, `scripts/build_serial.py`, and this README.

Commit history: `d189594` is the only upstream commit; later commits are ours. The git author recorded on
`d189594` is `Claude <noreply@anthropic.com>` (as committed upstream, with the trailer `Co-Authored-By: Claude Opus
5.5`); we have not altered it.

## Repository layout

| Path | Content |
|---|---|
| `Collatz/Defs.lean`, `Statements.lean`, `HercherRhin.lean` | the statement |
| `Collatz/Hercher*.lean`, `FareyCertificate.lean`, `LogTwoThreeBounds.lean` | Hercher's m <= 91 (Alick) |
| `Collatz/TwoRiseCheck{,2,3}.lean`, `MCycleSteps.lean`, `MCycleChain.lean`, `MCycleWalk.lean` | two-rise bound, chain, walk |
| `Collatz/ThreeRiseCheck.lean`, `MCycleSteps3.lean`, `MCycleChain3.lean` | three-rise bound, Lemma 3S, three-term chain (new) |
| `Collatz/TwoRise2_*.lean`, `MCycleThreeRise*.lean`, `MCycleGrid*.lean` | kernel-checked rise bounds (new) |
| `Collatz/MCycle92.lean` ... `MCycle110*.lean`, `WalkSplit.lean` | shapes, walks, certificates, main theorems |
| `scripts/Statement.lean`, `AxiomAudit.lean`, `build_serial.py` | statement check, axiom audit, serial build |
| `research/scripts/` | generators of the Lean data modules |
| `computed/` | Python reproducing m <= 127, with certificates and referee code (`computed/README.md`) |
| `METHOD.md` | the mathematics, and what is formalised |
| `AXIOM_AUDIT.txt` | recorded output of the axiom checks for m <= 111 |

## License

Apache License 2.0 (`LICENSE`); see `NOTICE` for copyright and a statement of changes.

## Disclosure: this work was generated by AI

**The new work in this repository (everything listed as new in "What is Alick's and what is new" above: the Lean code, the generated
certificate modules, the Python computations, the proofs in `METHOD.md`, and this text) was generated by an AI
system, Claude (Anthropic), working in Claude Code under the direction of Lee Marshall
([@LeeMarshall1113](https://github.com/LeeMarshall1113)).** The Lean parts are checked by the Lean kernel, so
their correctness does not depend on trusting the generator; the *statement* they prove should be read by a human
(see `scripts/Statement.lean`). The computed m <= 127 part is checked only by independent re-computation, also
AI-written, and has had no human referee. This is **not peer reviewed**. The repository builds on the Lean
project of Justin Alick, which was itself prepared with an AI assistant; see "What is Alick's and what is new".

This is not a proof of the Collatz conjecture. It rules out cycles with few local minima and says nothing about
cycles with more, or about divergent orbits.
