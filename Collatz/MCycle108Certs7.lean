import Collatz.MCycle108Certs6

/-!
# Certificates of the listed shapes of `data108`, chunks 24..27
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_24 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_24 = true := by
  decide +kernel

theorem certs108_25 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_25 = true := by
  decide +kernel

theorem certs108_26 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_26 = true := by
  decide +kernel

theorem certs108_27 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_27 = true := by
  decide +kernel

end Collatz
