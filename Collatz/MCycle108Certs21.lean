import Collatz.MCycle108Certs20

/-!
# Certificates of the listed shapes of `data108`, chunks 80..83
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_80 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_80 = true := by
  decide +kernel

theorem certs108_81 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_81 = true := by
  decide +kernel

theorem certs108_82 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_82 = true := by
  decide +kernel

theorem certs108_83 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_83 = true := by
  decide +kernel

end Collatz
