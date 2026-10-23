import Collatz.MCycle109Certs61

/-!
# Certificates of the listed shapes of `data109`, chunks 244..247
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_244 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_244 = true := by
  decide +kernel

theorem certs109_245 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_245 = true := by
  decide +kernel

theorem certs109_246 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_246 = true := by
  decide +kernel

theorem certs109_247 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_247 = true := by
  decide +kernel

end Collatz
