import Collatz.MCycle108Certs36

/-!
# Certificates of the listed shapes of `data108`, chunks 144..147
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_144 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_144 = true := by
  decide +kernel

theorem certs108_145 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_145 = true := by
  decide +kernel

theorem certs108_146 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_146 = true := by
  decide +kernel

theorem certs108_147 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_147 = true := by
  decide +kernel

end Collatz
