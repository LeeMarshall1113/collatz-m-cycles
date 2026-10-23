import Collatz.MCycle109Certs68

/-!
# Certificates of the listed shapes of `data109`, chunks 272..275
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_272 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_272 = true := by
  decide +kernel

theorem certs109_273 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_273 = true := by
  decide +kernel

theorem certs109_274 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_274 = true := by
  decide +kernel

theorem certs109_275 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_275 = true := by
  decide +kernel

end Collatz
