import Collatz.MCycle108Certs23

/-!
# Certificates of the listed shapes of `data108`, chunks 92..95
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_92 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_92 = true := by
  decide +kernel

theorem certs108_93 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_93 = true := by
  decide +kernel

theorem certs108_94 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_94 = true := by
  decide +kernel

theorem certs108_95 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_95 = true := by
  decide +kernel

end Collatz
