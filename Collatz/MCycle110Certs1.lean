import Collatz.MCycle110Shapes
import Collatz.MCycleGrid110
import Collatz.MCycleGrid3_107

/-!
# Certificates of the listed shapes of `data110`, chunks 0..3
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_0 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_0 = true := by
  decide +kernel

theorem certs110_1 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_1 = true := by
  decide +kernel

theorem certs110_2 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_2 = true := by
  decide +kernel

theorem certs110_3 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_3 = true := by
  decide +kernel

end Collatz
