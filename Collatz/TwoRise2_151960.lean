import Collatz.TwoRise2_151960_1
import Collatz.TwoRise2_151960_2
import Collatz.TwoRise2_151960_3
import Collatz.TwoRise2_151960_4
import Collatz.TwoRise2_151960_5
import Collatz.TwoRise2_151960_6
import Collatz.TwoRise2_151960_7
import Collatz.TwoRise2_151960_8
import Collatz.TwoRise2_151960_9
import Collatz.TwoRise2_151960_10
import Collatz.TwoRise2_151960_11

/-!
# `AllPairs 151960 151978` (linear-time checker, 507 chunks in 11 modules)
-/

namespace Collatz.TwoRise2

open Collatz.TwoRise

theorem allPairs151960 : AllPairs 151960 151978 := allPairs_of_range (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans rc151960_1 rc151960_2) rc151960_3) rc151960_4) rc151960_5) rc151960_6) rc151960_7) rc151960_8) rc151960_9) rc151960_10) rc151960_11)

end Collatz.TwoRise2
