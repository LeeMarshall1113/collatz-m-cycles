import Collatz.MCycle108Certs10

/-!
# Certificates of the listed shapes of `data108`, chunks 40..43
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_40 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_40 = true := by
  decide +kernel

theorem certs108_41 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_41 = true := by
  decide +kernel

theorem certs108_42 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_42 = true := by
  decide +kernel

theorem certs108_43 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_43 = true := by
  decide +kernel

end Collatz
