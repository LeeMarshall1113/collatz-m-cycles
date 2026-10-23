import Collatz.MCycle109Certs55

/-!
# Certificates of the listed shapes of `data109`, chunks 220..223
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_220 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_220 = true := by
  decide +kernel

theorem certs109_221 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_221 = true := by
  decide +kernel

theorem certs109_222 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_222 = true := by
  decide +kernel

theorem certs109_223 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_223 = true := by
  decide +kernel

end Collatz
