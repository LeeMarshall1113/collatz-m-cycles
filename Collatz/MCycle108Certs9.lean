import Collatz.MCycle108Certs8

/-!
# Certificates of the listed shapes of `data108`, chunks 32..35
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_32 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_32 = true := by
  decide +kernel

theorem certs108_33 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_33 = true := by
  decide +kernel

theorem certs108_34 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_34 = true := by
  decide +kernel

theorem certs108_35 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_35 = true := by
  decide +kernel

end Collatz
