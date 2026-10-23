import Collatz.MCycle108Certs37

/-!
# Certificates of the listed shapes of `data108`, chunks 148..151
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_148 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_148 = true := by
  decide +kernel

theorem certs108_149 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_149 = true := by
  decide +kernel

theorem certs108_150 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_150 = true := by
  decide +kernel

theorem certs108_151 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_151 = true := by
  decide +kernel

end Collatz
