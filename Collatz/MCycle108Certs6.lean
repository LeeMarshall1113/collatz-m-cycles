import Collatz.MCycle108Certs5

/-!
# Certificates of the listed shapes of `data108`, chunks 20..23
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_20 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_20 = true := by
  decide +kernel

theorem certs108_21 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_21 = true := by
  decide +kernel

theorem certs108_22 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_22 = true := by
  decide +kernel

theorem certs108_23 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_23 = true := by
  decide +kernel

end Collatz
