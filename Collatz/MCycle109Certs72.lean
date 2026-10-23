import Collatz.MCycle109Certs71

/-!
# Certificates of the listed shapes of `data109`, chunks 284..287
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_284 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_284 = true := by
  decide +kernel

theorem certs109_285 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_285 = true := by
  decide +kernel

theorem certs109_286 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_286 = true := by
  decide +kernel

theorem certs109_287 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_287 = true := by
  decide +kernel

end Collatz
