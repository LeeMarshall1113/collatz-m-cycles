import Collatz.MCycle108Certs39

/-!
# Certificates of the listed shapes of `data108`, chunks 156..159
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_156 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_156 = true := by
  decide +kernel

theorem certs108_157 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_157 = true := by
  decide +kernel

theorem certs108_158 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_158 = true := by
  decide +kernel

theorem certs108_159 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_159 = true := by
  decide +kernel

end Collatz
