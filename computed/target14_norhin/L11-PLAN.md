# L11 plan: `noRhin_of_effMeasure100`

## Assessment of the earlier plan

`EffMeasure100` (threshold `10^100`) does not imply `EffMeasure` (threshold `10^36`): the range
`10^36 <= K < 10^100` is missing. But the earlier plan overstates the work. Re-running `ceilOK` and
the whole NoRhin chain at `10^100` is not needed: `NoRhin.lean` uses `EffMeasure` only through
`K_lt_of_ceilOK`, so it is enough to **derive `EffMeasure` from `EffMeasure100` plus an unconditional
middle-range lemma** and feed it to the existing `no_111_cycle_2_71_eff`. No change to `ceilOK`,
`fareySegs`, `NoRhin.lean`.

## The statement needed (middle range)

For all `p`, all `K` with `10^36 <= K < 10^100`:
`exp(-K/2^80) < |p log 2 - K log 3|`.

Slack is enormous: `exp(-K/2^80) <= exp(-1000) <= 2^-1000` already for `K >= 10^36`
(`K/2^80 >= 8e11`), while `|p log 2 - K log 3| >= 0.69 K * mg` with `mg` about `1/(K^2 a)` (about
`10^-200` at the top). So no cleverness is needed; only the best-approximation property of the
convergents of `log2 3`, i.e. Farey segments.

## Certification

- Farey neighbours `a/b < delta < c/d` (consecutive convergents, from a script). For `K < b+d`, every
  `p/K` is `<= a/b` or `>= c/d` (existing `farey_den_bound_div`), so
  `|p - K delta| >= K * mg`, `mg = min(lo - a/b, c/d - hi)` against a rational enclosure `[lo, hi]`.
- Per segment, an exact rational check: `1 < 0.6931471803 * L * mg * 2^1000` and `1000*2^80 <= L`
  (`L` = start of the segment). This also covers p/K equal to an end (both sides handled).
- Enclosure: `deltaLo215/deltaHi215`, width `10^-215`, from the same `logSum` method as
  `LogTwoThreeBounds80` (n = 730 for log 2, 460 for log 3). Cross-checked in the generator against
  mpmath (400 digits) and an independent Machin-type atanh series.
- 207 convergent segments to denominators above `10^100`, 135 of them above `10^36`.
- All by `decide +kernel` on rationals; no `native_decide`.

## Cost estimate

Kernel: a few minutes at most (rational arithmetic on 100-200 digit numbers; the existing 73-segment
check takes seconds). Memory: ordinary Mathlib import (< 6 GB). Generated files: about 40 KB
(`MidRangeData.lean`) and 4 KB (`LogTwoThreeBounds215.lean`). Well inside budget.

## Files

- `computed/target14_norhin/l11/gen_l11.py` (+ two templates): generator and cross-checks.
- `Collatz/LogTwoThreeBounds215.lean`, `Collatz/MidRangeData.lean`: generated.
- `Collatz/MidRange.lean`: soundness (`midChain_sound`, `midRange`, `effMeasure_of_100`).
- `Collatz/Gelfond/Main.lean`: `noRhin_of_effMeasure100` becomes
  `no_111_cycle_2_71_eff hX (effMeasure_of_100 hE)`.
