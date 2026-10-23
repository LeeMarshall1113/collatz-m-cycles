import Collatz.MCycle106Shapes
import Collatz.MCycleGrid103
import Collatz.MCycleGrid3_107

/-!
# Certificates of the listed shapes of `data106`, chunks 0..11
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs106_0 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_0 = true := by
  decide +kernel

theorem certs106_1 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_1 = true := by
  decide +kernel

theorem certs106_2 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_2 = true := by
  decide +kernel

theorem certs106_3 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_3 = true := by
  decide +kernel

theorem certs106_4 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_4 = true := by
  decide +kernel

theorem certs106_5 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_5 = true := by
  decide +kernel

theorem certs106_6 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_6 = true := by
  decide +kernel

theorem certs106_7 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_7 = true := by
  decide +kernel

theorem certs106_8 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_8 = true := by
  decide +kernel

theorem certs106_9 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_9 = true := by
  decide +kernel

theorem certs106_10 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_10 = true := by
  decide +kernel

theorem certs106_11 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_11 = true := by
  decide +kernel

end Collatz
