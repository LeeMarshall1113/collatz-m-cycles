import Collatz.MCycle108Certs31

/-!
# Certificates of the listed shapes of `data108`, chunks 124..127
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_124 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_124 = true := by
  decide +kernel

theorem certs108_125 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_125 = true := by
  decide +kernel

theorem certs108_126 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_126 = true := by
  decide +kernel

theorem certs108_127 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_127 = true := by
  decide +kernel

end Collatz
