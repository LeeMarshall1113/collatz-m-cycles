import Collatz.TwoRise2_97951_1
import Collatz.TwoRise2_97951_2
import Collatz.TwoRise2_97951_3
import Collatz.TwoRise2_97951_4
import Collatz.TwoRise2_97951_5
import Collatz.TwoRise2_97951_6
import Collatz.TwoRise2_97951_7

/-!
# `AllPairs 97951 97965` (linear-time checker, 245 chunks in 7 modules)
-/

namespace Collatz.TwoRise2

open Collatz.TwoRise

theorem allPairs97951 : AllPairs 97951 97965 := allPairs_of_range (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans (RangeCond.trans rc97951_1 rc97951_2) rc97951_3) rc97951_4) rc97951_5) rc97951_6) rc97951_7)

end Collatz.TwoRise2
