import Collatz.MCycle108Certs28

/-!
# Certificates of the listed shapes of `data108`, chunks 112..115
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_112 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_112 = true := by
  decide +kernel

theorem certs108_113 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_113 = true := by
  decide +kernel

theorem certs108_114 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_114 = true := by
  decide +kernel

theorem certs108_115 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_115 = true := by
  decide +kernel

end Collatz
