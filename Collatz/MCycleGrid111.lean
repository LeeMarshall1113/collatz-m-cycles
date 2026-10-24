import Collatz.MCycleGrid110

/-!
# Two-rise grid `grid111` (= `grid110`)
-/

namespace Collatz

def grid111 : List (ℕ × ℕ) := grid110

theorem grid111_ok : ∀ e ∈ grid111, TwoRiseBound e.1 e.2 := grid110_ok

end Collatz
