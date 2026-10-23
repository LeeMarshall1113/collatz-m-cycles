import Collatz.MCycle109Certs63

/-!
# Certificates of the listed shapes of `data109`, chunks 252..255
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_252 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_252 = true := by
  decide +kernel

theorem certs109_253 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_253 = true := by
  decide +kernel

theorem certs109_254 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_254 = true := by
  decide +kernel

theorem certs109_255 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_255 = true := by
  decide +kernel

end Collatz
