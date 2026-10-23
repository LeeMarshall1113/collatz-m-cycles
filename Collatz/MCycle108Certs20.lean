import Collatz.MCycle108Certs19

/-!
# Certificates of the listed shapes of `data108`, chunks 76..79
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_76 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_76 = true := by
  decide +kernel

theorem certs108_77 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_77 = true := by
  decide +kernel

theorem certs108_78 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_78 = true := by
  decide +kernel

theorem certs108_79 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_79 = true := by
  decide +kernel

end Collatz
