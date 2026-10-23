import Collatz.MCycle108Certs25

/-!
# Certificates of the listed shapes of `data108`, chunks 100..103
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_100 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_100 = true := by
  decide +kernel

theorem certs108_101 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_101 = true := by
  decide +kernel

theorem certs108_102 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_102 = true := by
  decide +kernel

theorem certs108_103 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_103 = true := by
  decide +kernel

end Collatz
