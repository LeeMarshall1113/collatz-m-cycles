import Collatz.MCycle108Certs24

/-!
# Certificates of the listed shapes of `data108`, chunks 96..99
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_96 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_96 = true := by
  decide +kernel

theorem certs108_97 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_97 = true := by
  decide +kernel

theorem certs108_98 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_98 = true := by
  decide +kernel

theorem certs108_99 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_99 = true := by
  decide +kernel

end Collatz
