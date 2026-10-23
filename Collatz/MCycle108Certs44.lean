import Collatz.MCycle108Certs43

/-!
# Certificates of the listed shapes of `data108`, chunks 172..175
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_172 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_172 = true := by
  decide +kernel

theorem certs108_173 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_173 = true := by
  decide +kernel

theorem certs108_174 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_174 = true := by
  decide +kernel

theorem certs108_175 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_175 = true := by
  decide +kernel

end Collatz
