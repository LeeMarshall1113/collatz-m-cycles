import Collatz.MCycle108Certs14

/-!
# Certificates of the listed shapes of `data108`, chunks 56..59
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_56 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_56 = true := by
  decide +kernel

theorem certs108_57 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_57 = true := by
  decide +kernel

theorem certs108_58 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_58 = true := by
  decide +kernel

theorem certs108_59 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_59 = true := by
  decide +kernel

end Collatz
