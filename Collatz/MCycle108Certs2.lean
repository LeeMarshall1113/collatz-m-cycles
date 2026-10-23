import Collatz.MCycle108Certs1

/-!
# Certificates of the listed shapes of `data108`, chunks 4..7
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_4 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_4 = true := by
  decide +kernel

theorem certs108_5 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_5 = true := by
  decide +kernel

theorem certs108_6 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_6 = true := by
  decide +kernel

theorem certs108_7 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_7 = true := by
  decide +kernel

end Collatz
