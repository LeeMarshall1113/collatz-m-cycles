import Collatz.MCycle108Certs16

/-!
# Certificates of the listed shapes of `data108`, chunks 64..67
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_64 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_64 = true := by
  decide +kernel

theorem certs108_65 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_65 = true := by
  decide +kernel

theorem certs108_66 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_66 = true := by
  decide +kernel

theorem certs108_67 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_67 = true := by
  decide +kernel

end Collatz
