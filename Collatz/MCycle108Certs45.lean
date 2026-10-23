import Collatz.MCycle108Certs44

/-!
# Certificates of the listed shapes of `data108`, chunks 176..179
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_176 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_176 = true := by
  decide +kernel

theorem certs108_177 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_177 = true := by
  decide +kernel

theorem certs108_178 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_178 = true := by
  decide +kernel

theorem certs108_179 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_179 = true := by
  decide +kernel

end Collatz
