import Collatz.MCycle108Certs9

/-!
# Certificates of the listed shapes of `data108`, chunks 36..39
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_36 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_36 = true := by
  decide +kernel

theorem certs108_37 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_37 = true := by
  decide +kernel

theorem certs108_38 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_38 = true := by
  decide +kernel

theorem certs108_39 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_39 = true := by
  decide +kernel

end Collatz
