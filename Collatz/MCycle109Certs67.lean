import Collatz.MCycle109Certs66

/-!
# Certificates of the listed shapes of `data109`, chunks 264..267
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_264 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_264 = true := by
  decide +kernel

theorem certs109_265 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_265 = true := by
  decide +kernel

theorem certs109_266 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_266 = true := by
  decide +kernel

theorem certs109_267 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_267 = true := by
  decide +kernel

end Collatz
