import Collatz.MCycle109Certs67

/-!
# Certificates of the listed shapes of `data109`, chunks 268..271
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_268 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_268 = true := by
  decide +kernel

theorem certs109_269 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_269 = true := by
  decide +kernel

theorem certs109_270 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_270 = true := by
  decide +kernel

theorem certs109_271 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_271 = true := by
  decide +kernel

end Collatz
