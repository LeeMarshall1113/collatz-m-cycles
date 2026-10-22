import Collatz.MCycle105Shapes
import Collatz.MCycleGrid103
import Collatz.MCycleGrid3_105

/-!
# Certificates of the listed shapes of `data105`, chunks 0..3
-/

set_option Elab.async false

namespace Collatz

theorem certs105_0 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_0 = true := by
  decide +kernel

theorem certs105_1 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_1 = true := by
  decide +kernel

theorem certs105_2 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_2 = true := by
  decide +kernel

theorem certs105_3 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_3 = true := by
  decide +kernel

end Collatz
