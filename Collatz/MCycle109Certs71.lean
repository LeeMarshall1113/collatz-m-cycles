import Collatz.MCycle109Certs70

/-!
# Certificates of the listed shapes of `data109`, chunks 280..283
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_280 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_280 = true := by
  decide +kernel

theorem certs109_281 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_281 = true := by
  decide +kernel

theorem certs109_282 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_282 = true := by
  decide +kernel

theorem certs109_283 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_283 = true := by
  decide +kernel

end Collatz
