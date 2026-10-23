import Collatz.MCycle108Certs45

/-!
# Certificates of the listed shapes of `data108`, chunks 180..183
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_180 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_180 = true := by
  decide +kernel

theorem certs108_181 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_181 = true := by
  decide +kernel

theorem certs108_182 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_182 = true := by
  decide +kernel

theorem certs108_183 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_183 = true := by
  decide +kernel

end Collatz
