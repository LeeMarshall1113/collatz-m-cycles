import Collatz.MCycle108Certs21

/-!
# Certificates of the listed shapes of `data108`, chunks 84..87
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_84 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_84 = true := by
  decide +kernel

theorem certs108_85 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_85 = true := by
  decide +kernel

theorem certs108_86 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_86 = true := by
  decide +kernel

theorem certs108_87 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_87 = true := by
  decide +kernel

end Collatz
