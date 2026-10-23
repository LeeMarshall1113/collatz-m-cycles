import Collatz.MCycle108Certs12

/-!
# Certificates of the listed shapes of `data108`, chunks 48..51
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_48 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_48 = true := by
  decide +kernel

theorem certs108_49 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_49 = true := by
  decide +kernel

theorem certs108_50 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_50 = true := by
  decide +kernel

theorem certs108_51 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_51 = true := by
  decide +kernel

end Collatz
