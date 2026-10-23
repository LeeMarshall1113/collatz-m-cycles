import Collatz.MCycle108Certs3

/-!
# Certificates of the listed shapes of `data108`, chunks 12..15
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_12 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_12 = true := by
  decide +kernel

theorem certs108_13 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_13 = true := by
  decide +kernel

theorem certs108_14 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_14 = true := by
  decide +kernel

theorem certs108_15 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_15 = true := by
  decide +kernel

end Collatz
