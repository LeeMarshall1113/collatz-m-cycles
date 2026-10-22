import Collatz.MCycleSteps3
import Collatz.MCycleThreeRise105

/-!
# The three-rise grid for `m = 104, 105`
-/

namespace Collatz

/-- The three-rise bounds `(N, B)` (increasing `N`). -/
def grid3_105 : List (ℕ × ℕ) := [(79, 88), (122, 135)]

theorem grid3_105_ok : ∀ e ∈ grid3_105, ThreeRiseBound e.1 e.2 := by
  intro e he
  rcases List.mem_cons.mp he with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples79
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples122
  · cases h

end Collatz
