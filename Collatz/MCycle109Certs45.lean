import Collatz.MCycle109Certs44

/-!
# Certificates of the listed shapes of `data109`, chunks 176..179
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_176 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_176 = true := by
  decide +kernel

theorem certs109_177 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_177 = true := by
  decide +kernel

theorem certs109_178 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_178 = true := by
  decide +kernel

theorem certs109_179 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_179 = true := by
  decide +kernel

end Collatz
