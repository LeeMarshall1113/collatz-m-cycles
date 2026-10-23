import Collatz.MCycle109Certs39

/-!
# Certificates of the listed shapes of `data109`, chunks 156..159
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_156 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_156 = true := by
  decide +kernel

theorem certs109_157 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_157 = true := by
  decide +kernel

theorem certs109_158 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_158 = true := by
  decide +kernel

theorem certs109_159 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_159 = true := by
  decide +kernel

end Collatz
