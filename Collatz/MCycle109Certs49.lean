import Collatz.MCycle109Certs48

/-!
# Certificates of the listed shapes of `data109`, chunks 192..195
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_192 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_192 = true := by
  decide +kernel

theorem certs109_193 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_193 = true := by
  decide +kernel

theorem certs109_194 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_194 = true := by
  decide +kernel

theorem certs109_195 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_195 = true := by
  decide +kernel

end Collatz
