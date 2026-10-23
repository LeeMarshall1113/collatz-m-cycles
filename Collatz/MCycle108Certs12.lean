import Collatz.MCycle108Certs11

/-!
# Certificates of the listed shapes of `data108`, chunks 44..47
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_44 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_44 = true := by
  decide +kernel

theorem certs108_45 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_45 = true := by
  decide +kernel

theorem certs108_46 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_46 = true := by
  decide +kernel

theorem certs108_47 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_47 = true := by
  decide +kernel

end Collatz
