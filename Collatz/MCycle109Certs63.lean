import Collatz.MCycle109Certs62

/-!
# Certificates of the listed shapes of `data109`, chunks 248..251
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_248 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_248 = true := by
  decide +kernel

theorem certs109_249 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_249 = true := by
  decide +kernel

theorem certs109_250 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_250 = true := by
  decide +kernel

theorem certs109_251 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_251 = true := by
  decide +kernel

end Collatz
