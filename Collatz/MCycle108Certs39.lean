import Collatz.MCycle108Certs38

/-!
# Certificates of the listed shapes of `data108`, chunks 152..155
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_152 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_152 = true := by
  decide +kernel

theorem certs108_153 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_153 = true := by
  decide +kernel

theorem certs108_154 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_154 = true := by
  decide +kernel

theorem certs108_155 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_155 = true := by
  decide +kernel

end Collatz
