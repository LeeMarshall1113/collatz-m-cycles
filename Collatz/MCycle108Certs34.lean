import Collatz.MCycle108Certs33

/-!
# Certificates of the listed shapes of `data108`, chunks 132..135
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_132 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_132 = true := by
  decide +kernel

theorem certs108_133 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_133 = true := by
  decide +kernel

theorem certs108_134 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_134 = true := by
  decide +kernel

theorem certs108_135 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_135 = true := by
  decide +kernel

end Collatz
