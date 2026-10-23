import Collatz.MCycle109
import Collatz.MCycle110Data

/-!
# No Collatz `m`-cycle with `m ≤ 110` when every `n ≤ 2⁷¹` reaches 1

`no_109_cycle_2_71` extended by `m = 110` (three-rise chain, `MCycleChain3.lean`). The three-rise grid
is `grid3_107`; the two-rise grid is `grid110` (`MCycleGrid110.lean`): `grid109` and the new
points `247533, 384012, 403213, 647476` (linear-time checker, `TwoRiseCheck2.lean`).

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 110`** when every `0 < n ≤ 2 ^ 71` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 111 local minima. -/
theorem no_110_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 111 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h109' := no_109_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h110 := no_110_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
