import Collatz.MCycle108Certs40

/-!
# Certificates of the listed shapes of `data108`, chunks 160..163
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_160 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_160 = true := by
  decide +kernel

theorem certs108_161 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_161 = true := by
  decide +kernel

theorem certs108_162 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_162 = true := by
  decide +kernel

theorem certs108_163 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_163 = true := by
  decide +kernel

end Collatz
