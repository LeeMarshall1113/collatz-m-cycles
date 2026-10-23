import Collatz.MCycleGrid103
import Collatz.TwoRise2_97951

/-!
# Two-rise grid `grid108`: `grid103` and the new point `97951` (linear-time checker, `TwoRiseCheck2.lean`)
-/

namespace Collatz

/-- The two-rise bounds `(N, B)` (increasing `N`). -/
def grid108 : List (ℕ × ℕ) := grid103 ++ [(97951, 97965)]

theorem grid108_ok : ∀ e ∈ grid108, TwoRiseBound e.1 e.2 := by
  intro e h
  unfold grid108 at h
  rcases List.mem_append.mp h with h | h
  · exact grid103_ok e h
  · rcases List.mem_singleton.mp h with rfl
    exact twoRiseBound_of_allPairs TwoRise2.allPairs97951

end Collatz
