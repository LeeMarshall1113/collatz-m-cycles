import Collatz.MCycle108Certs4

/-!
# Certificates of the listed shapes of `data108`, chunks 16..19
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_16 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_16 = true := by
  decide +kernel

theorem certs108_17 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_17 = true := by
  decide +kernel

theorem certs108_18 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_18 = true := by
  decide +kernel

theorem certs108_19 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_19 = true := by
  decide +kernel

end Collatz
