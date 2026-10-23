import Collatz.MCycle108Certs18

/-!
# Certificates of the listed shapes of `data108`, chunks 72..75
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_72 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_72 = true := by
  decide +kernel

theorem certs108_73 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_73 = true := by
  decide +kernel

theorem certs108_74 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_74 = true := by
  decide +kernel

theorem certs108_75 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_75 = true := by
  decide +kernel

end Collatz
