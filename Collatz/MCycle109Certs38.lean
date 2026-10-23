import Collatz.MCycle109Certs37

/-!
# Certificates of the listed shapes of `data109`, chunks 148..151
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_148 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_148 = true := by
  decide +kernel

theorem certs109_149 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_149 = true := by
  decide +kernel

theorem certs109_150 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_150 = true := by
  decide +kernel

theorem certs109_151 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_151 = true := by
  decide +kernel

end Collatz
