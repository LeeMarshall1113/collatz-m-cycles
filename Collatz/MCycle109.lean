import Collatz.MCycle108
import Collatz.MCycle109Data

/-!
# No Collatz `m`-cycle with `m ≤ 109` when every `n ≤ 2⁷¹` reaches 1

`no_108_cycle_2_71` extended by `m = 109` (three-rise chain, `MCycleChain3.lean`). The three-rise grid
is `grid3_107`; the two-rise grid is `grid109` (`MCycleGrid109.lean`): `grid108` and the new
point `(151960, 151978)` (`MCycleTwoRise109.lean`).

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 109`** when every `0 < n ≤ 2 ^ 71` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 110 local minima. -/
theorem no_109_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 110 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h108 := no_108_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h109 := no_109_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
