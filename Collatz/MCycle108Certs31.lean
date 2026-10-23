import Collatz.MCycle108Certs30

/-!
# Certificates of the listed shapes of `data108`, chunks 120..123
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_120 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_120 = true := by
  decide +kernel

theorem certs108_121 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_121 = true := by
  decide +kernel

theorem certs108_122 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_122 = true := by
  decide +kernel

theorem certs108_123 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_123 = true := by
  decide +kernel

end Collatz
