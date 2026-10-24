import Collatz.MCycleSteps3
import Collatz.MCycleGrid3_107
import Collatz.MCycleThreeRiseN498_1
import Collatz.MCycleThreeRiseN498_2
import Collatz.MCycleThreeRiseN498_3
import Collatz.MCycleThreeRiseN498_4
import Collatz.MCycleThreeRiseN498_5
import Collatz.MCycleThreeRiseN498_6
import Collatz.MCycleThreeRiseN498_7
import Collatz.MCycleThreeRiseN498_8
import Collatz.MCycleThreeRiseN498_9
import Collatz.MCycleThreeRiseN498_10
import Collatz.MCycleThreeRiseN522_1
import Collatz.MCycleThreeRiseN522_2
import Collatz.MCycleThreeRiseN522_3
import Collatz.MCycleThreeRiseN522_4
import Collatz.MCycleThreeRiseN522_5
import Collatz.MCycleThreeRiseN522_6
import Collatz.MCycleThreeRiseN522_7
import Collatz.MCycleThreeRiseN522_8
import Collatz.MCycleThreeRiseN522_9
import Collatz.MCycleThreeRiseN522_10
import Collatz.MCycleThreeRiseN522_11
import Collatz.MCycleThreeRiseN522_12

/-!
# The three-rise grid for `m = 111`

Generated; the `AllTriples` of the new points are joined from their parts here.
-/

namespace Collatz

/-- `k₀ + k₁ + k₂ ≤ 512` for the first three rises from every odd `n < 2^498`. -/
theorem ThreeRise.allTriples498 : ThreeRise.AllTriples 498 512 :=
  ThreeRise.allTriples_of_range ((((((((((ThreeRise.rt498_17).trans ThreeRise.rt498_35).trans ThreeRise.rt498_55).trans ThreeRise.rt498_77).trans ThreeRise.rt498_102).trans ThreeRise.rt498_130).trans ThreeRise.rt498_164).trans ThreeRise.rt498_206).trans ThreeRise.rt498_266).trans ThreeRise.rt498_402)

/-- `k₀ + k₁ + k₂ ≤ 539` for the first three rises from every odd `n < 2^522`. -/
theorem ThreeRise.allTriples522 : ThreeRise.AllTriples 522 539 :=
  ThreeRise.allTriples_of_range ((((((((((((ThreeRise.rt522_14).trans ThreeRise.rt522_30).trans ThreeRise.rt522_47).trans ThreeRise.rt522_65).trans ThreeRise.rt522_85).trans ThreeRise.rt522_107).trans ThreeRise.rt522_131).trans ThreeRise.rt522_159).trans ThreeRise.rt522_192).trans ThreeRise.rt522_234).trans ThreeRise.rt522_293).trans ThreeRise.rt522_426)

/-- The three-rise bounds `(N, B)` (increasing `N`). -/
def grid3_111 : List (ℕ × ℕ) := [(79, 88), (122, 135), (203, 216), (325, 340), (498, 512), (522, 539)]

theorem grid3_111_ok : ∀ e ∈ grid3_111, ThreeRiseBound e.1 e.2 := by
  intro e h
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples79
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples122
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples203
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples325
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples498
  rcases List.mem_cons.mp h with h | h
  · rw [h]; exact threeRiseBound_of_allTriples ThreeRise.allTriples522
  · cases h

end Collatz
