import Collatz.MCycle109Certs49

/-!
# Certificates of the listed shapes of `data109`, chunks 196..199
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_196 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_196 = true := by
  decide +kernel

theorem certs109_197 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_197 = true := by
  decide +kernel

theorem certs109_198 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_198 = true := by
  decide +kernel

theorem certs109_199 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_199 = true := by
  decide +kernel

end Collatz
