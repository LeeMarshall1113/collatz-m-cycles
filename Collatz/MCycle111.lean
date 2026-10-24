import Collatz.MCycle110
import Collatz.MCycle111Data

/-!
# No Collatz `m`-cycle with `m ≤ 111` when every `n ≤ 2⁷¹` reaches 1

`no_110_cycle_2_71` extended by `m = 111` (three-rise chain). The two-rise grid is `grid111 = grid110`;
the three-rise grid is `grid3_111` (`grid3_107` with 498 and 522); the shape certificates use the 80-digit
enclosure of `log₂ 3` (`MCycleChain3D.lean`, `LogTwoThreeBounds80.lean`).

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 111`** when every `0 < n ≤ 2 ^ 71` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 112 local minima. -/
theorem no_111_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 112 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h110' := no_110_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h111 := no_111_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
