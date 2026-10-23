import Collatz.MCycle108Shapes
import Collatz.MCycleGrid108
import Collatz.MCycleGrid3_107

/-!
# Certificates of the listed shapes of `data108`, chunks 0..3
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_0 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_0 = true := by
  decide +kernel

theorem certs108_1 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_1 = true := by
  decide +kernel

theorem certs108_2 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_2 = true := by
  decide +kernel

theorem certs108_3 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_3 = true := by
  decide +kernel

end Collatz
