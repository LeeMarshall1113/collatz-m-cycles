import Collatz.MCycle109Certs57

/-!
# Certificates of the listed shapes of `data109`, chunks 228..231
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_228 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_228 = true := by
  decide +kernel

theorem certs109_229 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_229 = true := by
  decide +kernel

theorem certs109_230 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_230 = true := by
  decide +kernel

theorem certs109_231 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_231 = true := by
  decide +kernel

end Collatz
