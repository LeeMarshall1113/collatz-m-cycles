import Collatz.MCycle108Certs17

/-!
# Certificates of the listed shapes of `data108`, chunks 68..71
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_68 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_68 = true := by
  decide +kernel

theorem certs108_69 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_69 = true := by
  decide +kernel

theorem certs108_70 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_70 = true := by
  decide +kernel

theorem certs108_71 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_71 = true := by
  decide +kernel

end Collatz
