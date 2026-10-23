import Collatz.MCycle108Certs7

/-!
# Certificates of the listed shapes of `data108`, chunks 28..31
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_28 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_28 = true := by
  decide +kernel

theorem certs108_29 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_29 = true := by
  decide +kernel

theorem certs108_30 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_30 = true := by
  decide +kernel

theorem certs108_31 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_31 = true := by
  decide +kernel

end Collatz
