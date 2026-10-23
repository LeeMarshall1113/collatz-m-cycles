import Collatz.MCycle107
import Collatz.MCycle108Data

/-!
# No Collatz `m`-cycle with `m ≤ 108` when every `n ≤ 2⁷¹` reaches 1

`no_107_cycle_2_71` extended by `m = 108` (three-rise chain, `MCycleChain3.lean`). The three-rise grid
is `grid3_107`; the two-rise grid is `grid108` (`MCycleGrid108.lean`): `grid103` and the new
point `(97951, 97965)` (`MCycleTwoRise108.lean`).

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 108`** when every `0 < n ≤ 2 ^ 71` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 109 local minima. -/
theorem no_108_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 109 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h107 := no_107_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h108 := no_108_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
