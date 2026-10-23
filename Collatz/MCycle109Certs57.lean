import Collatz.MCycle109Certs56

/-!
# Certificates of the listed shapes of `data109`, chunks 224..227
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_224 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_224 = true := by
  decide +kernel

theorem certs109_225 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_225 = true := by
  decide +kernel

theorem certs109_226 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_226 = true := by
  decide +kernel

theorem certs109_227 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_227 = true := by
  decide +kernel

end Collatz
