import Collatz.MCycle108Certs41

/-!
# Certificates of the listed shapes of `data108`, chunks 164..167
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_164 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_164 = true := by
  decide +kernel

theorem certs108_165 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_165 = true := by
  decide +kernel

theorem certs108_166 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_166 = true := by
  decide +kernel

theorem certs108_167 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_167 = true := by
  decide +kernel

end Collatz
