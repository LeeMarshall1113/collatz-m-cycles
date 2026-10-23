import Collatz.MCycle109Certs54

/-!
# Certificates of the listed shapes of `data109`, chunks 216..219
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_216 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_216 = true := by
  decide +kernel

theorem certs109_217 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_217 = true := by
  decide +kernel

theorem certs109_218 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_218 = true := by
  decide +kernel

theorem certs109_219 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_219 = true := by
  decide +kernel

end Collatz
