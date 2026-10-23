import Collatz.MCycle108Certs32

/-!
# Certificates of the listed shapes of `data108`, chunks 128..131
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_128 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_128 = true := by
  decide +kernel

theorem certs108_129 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_129 = true := by
  decide +kernel

theorem certs108_130 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_130 = true := by
  decide +kernel

theorem certs108_131 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_131 = true := by
  decide +kernel

end Collatz
