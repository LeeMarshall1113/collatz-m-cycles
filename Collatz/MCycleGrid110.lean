import Collatz.MCycleGrid109
import Collatz.TwoRise2_247533
import Collatz.TwoRise2_384012
import Collatz.TwoRise2_403213
import Collatz.TwoRise2_647476

/-!
# Two-rise grid `grid110`: `grid109` and the points `247533, 384012, 403213, 647476`

All four checked by the linear-time checker (`TwoRiseCheck2.lean`); the points are the ones the m = 110
chains use (collatz-loop research/target12_lean127/PLAN.md §2.1).
-/

namespace Collatz

/-- The two-rise bounds `(N, B)` (increasing `N`). -/
def grid110 : List (ℕ × ℕ) :=
  grid109 ++ [(247533, 247549), (384012, 384028), (403213, 403231), (647476, 647493)]

theorem grid110_ok : ∀ e ∈ grid110, TwoRiseBound e.1 e.2 := by
  intro e h
  unfold grid110 at h
  rcases List.mem_append.mp h with h | h
  · exact grid109_ok e h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact twoRiseBound_of_allPairs TwoRise2.allPairs247533
    · exact twoRiseBound_of_allPairs TwoRise2.allPairs384012
    · exact twoRiseBound_of_allPairs TwoRise2.allPairs403213
    · exact twoRiseBound_of_allPairs TwoRise2.allPairs647476

end Collatz
