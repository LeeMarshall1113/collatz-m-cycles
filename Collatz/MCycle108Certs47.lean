import Collatz.MCycle108Certs46

/-!
# Certificates of the listed shapes of `data108`, chunks 184..186
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_184 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_184 = true := by
  decide +kernel

theorem certs108_185 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_185 = true := by
  decide +kernel

theorem certs108_186 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_186 = true := by
  decide +kernel

end Collatz
