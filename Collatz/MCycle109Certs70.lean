import Collatz.MCycle109Certs69

/-!
# Certificates of the listed shapes of `data109`, chunks 276..279
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_276 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_276 = true := by
  decide +kernel

theorem certs109_277 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_277 = true := by
  decide +kernel

theorem certs109_278 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_278 = true := by
  decide +kernel

theorem certs109_279 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_279 = true := by
  decide +kernel

end Collatz
