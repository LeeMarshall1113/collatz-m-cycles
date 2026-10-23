import Collatz.MCycle109Certs65

/-!
# Certificates of the listed shapes of `data109`, chunks 260..263
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_260 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_260 = true := by
  decide +kernel

theorem certs109_261 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_261 = true := by
  decide +kernel

theorem certs109_262 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_262 = true := by
  decide +kernel

theorem certs109_263 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_263 = true := by
  decide +kernel

end Collatz
