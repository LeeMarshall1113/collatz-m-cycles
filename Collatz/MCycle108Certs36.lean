import Collatz.MCycle108Certs35

/-!
# Certificates of the listed shapes of `data108`, chunks 140..143
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_140 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_140 = true := by
  decide +kernel

theorem certs108_141 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_141 = true := by
  decide +kernel

theorem certs108_142 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_142 = true := by
  decide +kernel

theorem certs108_143 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_143 = true := by
  decide +kernel

end Collatz
