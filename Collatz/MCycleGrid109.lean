import Collatz.MCycleGrid108
import Collatz.TwoRise2_151960

/-!
# Two-rise grid `grid109`: `grid108` and the new point `151960`
-/

namespace Collatz

/-- The two-rise bounds `(N, B)` (increasing `N`). -/
def grid109 : List (ℕ × ℕ) := grid108 ++ [(151960, 151978)]

theorem grid109_ok : ∀ e ∈ grid109, TwoRiseBound e.1 e.2 := by
  intro e h
  unfold grid109 at h
  rcases List.mem_append.mp h with h | h
  · exact grid108_ok e h
  · rcases List.mem_singleton.mp h with rfl
    exact twoRiseBound_of_allPairs TwoRise2.allPairs151960

end Collatz
