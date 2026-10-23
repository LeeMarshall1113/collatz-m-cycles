import Collatz.MCycle106Certs6

/-!
# Certificates of the listed shapes of `data106`, chunks 72..76
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs106_72 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_72 = true := by
  decide +kernel

theorem certs106_73 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_73 = true := by
  decide +kernel

theorem certs106_74 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_74 = true := by
  decide +kernel

theorem certs106_75 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_75 = true := by
  decide +kernel

theorem certs106_76 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106_76 = true := by
  decide +kernel

end Collatz
