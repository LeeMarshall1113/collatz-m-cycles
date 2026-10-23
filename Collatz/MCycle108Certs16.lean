import Collatz.MCycle108Certs15

/-!
# Certificates of the listed shapes of `data108`, chunks 60..63
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_60 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_60 = true := by
  decide +kernel

theorem certs108_61 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_61 = true := by
  decide +kernel

theorem certs108_62 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_62 = true := by
  decide +kernel

theorem certs108_63 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_63 = true := by
  decide +kernel

end Collatz
