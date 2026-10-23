import Collatz.MCycle105
import Collatz.MCycle106Data
import Collatz.MCycle107Data

/-!
# No Collatz `m`-cycle with `m ≤ 107` when every `n ≤ 2⁷¹` reaches 1

`no_105_cycle_2_71` extended by `m = 106` and `m = 107`, each a separate exclusion with the
three-rise chain (`MCycleChain3.lean`). The three-rise grid is `grid3_107`: `AllTriples 79 88`,
`AllTriples 122 135` (`MCycleThreeRise105.lean`) and the new `AllTriples 203 216`,
`AllTriples 325 340` (`MCycleThreeRiseN203.lean`, `MCycleThreeRiseN325_1..3.lean`), all checked by
the kernel with the checker of `ThreeRiseCheck.lean`. The two-rise grid is `grid103`, unchanged.

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 106`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 107 local minima. -/
theorem no_106_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 107 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h105 := no_105_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h106 := no_106_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

/-- **No Collatz `m`-cycle with `m ≤ 107`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 108 local minima. -/
theorem no_107_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 108 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h106 := no_106_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h107 := no_107_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
