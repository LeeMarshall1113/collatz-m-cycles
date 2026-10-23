import Collatz.MCycle109Certs50

/-!
# Certificates of the listed shapes of `data109`, chunks 200..203
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_200 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_200 = true := by
  decide +kernel

theorem certs109_201 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_201 = true := by
  decide +kernel

theorem certs109_202 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_202 = true := by
  decide +kernel

theorem certs109_203 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_203 = true := by
  decide +kernel

end Collatz
