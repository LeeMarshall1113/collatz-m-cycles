import Collatz.MCycle103
import Collatz.MCycle104Data
import Collatz.MCycle105Data

/-!
# No Collatz `m`-cycle with `m ≤ 105` when every `n ≤ 2⁷¹` reaches 1

`no_103_cycle_2_71` extended by two more `m` with the three-rise chain (`MCycleChain3.lean`):
besides Alick's one- and two-step bounds, the chain of minima uses the three-step bound
(Lemma 3S, `logb_three_step`) with the three-rise bounds `AllTriples 79 88` and `AllTriples 122 135`
(kernel-checked in `MCycleThreeRise105.lean` by the checker of `ThreeRiseCheck.lean`). The two-rise
grid is `grid103`, unchanged.

The hypotheses are the verification bound `2⁷¹` (Bařina) and `RhinBound`; nothing else is assumed.
-/

namespace Collatz

/-- **No Collatz `m`-cycle with `m ≤ 105`** when every `0 < n ≤ 2⁷¹` reaches 1, given
`RhinBound`: every nontrivial positive `T`-cycle has at least 106 local minima. -/
theorem no_105_cycle_2_71 (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 106 ≤ numLocalMin x p := by
  intro x p hx hp hcyc hx1 hx2
  have h103 := no_103_cycle_2_71 hX hR x p hx hp hcyc hx1 hx2
  have hlow := cycle_gt_of_verified hX hx hp hcyc hx1 hx2
  have h104 := no_104_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  have h105 := no_105_cycle_of_floor hR hx hp hcyc hx1 hx2 hlow
  omega

end Collatz
