import Collatz.MCycle108Certs22

/-!
# Certificates of the listed shapes of `data108`, chunks 88..91
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_88 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_88 = true := by
  decide +kernel

theorem certs108_89 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_89 = true := by
  decide +kernel

theorem certs108_90 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_90 = true := by
  decide +kernel

theorem certs108_91 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_91 = true := by
  decide +kernel

end Collatz
