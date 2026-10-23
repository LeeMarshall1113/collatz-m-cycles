import Collatz.MCycleSteps3
import Collatz.MCycleThreeRise105
import Collatz.MCycleThreeRiseN203
import Collatz.MCycleThreeRiseN325_1
import Collatz.MCycleThreeRiseN325_2
import Collatz.MCycleThreeRiseN325_3

/-!
# The three-rise grid for `m = 106, 107`

Generated; the `AllTriples` of the new points are joined from their parts here.
-/

namespace Collatz

/-- `k₀ + k₁ + k₂ ≤ 216` for the first three rises from every odd `n < 2^203`. -/
theorem ThreeRise.allTriples203 : ThreeRise.AllTriples 203 216 :=
  ThreeRise.allTriples_of_range (ThreeRise.rt203_107)

/-- `k₀ + k₁ + k₂ ≤ 340` for the first three rises from every odd `n < 2^325`. -/
theorem ThreeRise.allTriples325 : ThreeRise.AllTriples 325 340 :=
  ThreeRise.allTriples_of_range (((ThreeRise.rt325_41).trans ThreeRise.rt325_99).trans ThreeRise.rt325_229)

/-- The three-rise bounds `(N, B)` (increasing `N`). -/
def grid3_107 : List (ℕ × ℕ) := [(79, 88), (122, 135), (203, 216), (325, 340)]

theorem grid3_107_ok : ∀ e ∈ grid3_107, ThreeRiseBound e.1 e.2 := by
  intro e h
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples79
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples122
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples203
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples325
  · cases h

end Collatz
