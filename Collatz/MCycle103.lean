import Collatz.MCycle102
import Collatz.MCycle103Data

/-!
# No Collatz `m`-cycle with `m ≤ 103` when every `n ≤ 2⁷¹` reaches 1

`no_102_cycle_2_71` extended by one more `m`: `MCycle103Data.lean` excludes `m = 103` by the same
chain bound, with the two-rise grid `grid103` = `grid102` plus the point `N = 60821`
(`AllPairs 60821 60836`, kernel-checked in `MCycleTwoRise103.lean`). The point is needed by the
shape `K = 77692117359936589403`, whose chain levels off above the top of `grid102` (`N = 37763`).

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 103`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 104 local minima. -/
theorem no_103_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 104 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h102 := no_102_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h103 := no_103_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
