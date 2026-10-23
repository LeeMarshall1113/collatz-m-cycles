import Collatz.MCycle109Certs58

/-!
# Certificates of the listed shapes of `data109`, chunks 232..235
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_232 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_232 = true := by
  decide +kernel

theorem certs109_233 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_233 = true := by
  decide +kernel

theorem certs109_234 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_234 = true := by
  decide +kernel

theorem certs109_235 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_235 = true := by
  decide +kernel

end Collatz
