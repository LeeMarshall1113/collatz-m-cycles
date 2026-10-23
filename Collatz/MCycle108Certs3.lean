import Collatz.MCycle108Certs2

/-!
# Certificates of the listed shapes of `data108`, chunks 8..11
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_8 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_8 = true := by
  decide +kernel

theorem certs108_9 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_9 = true := by
  decide +kernel

theorem certs108_10 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_10 = true := by
  decide +kernel

theorem certs108_11 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_11 = true := by
  decide +kernel

end Collatz
