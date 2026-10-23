import Collatz.MCycle109Certs5

/-!
# Certificates of the listed shapes of `data109`, chunks 20..23
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_20 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_20 = true := by
  decide +kernel

theorem certs109_21 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_21 = true := by
  decide +kernel

theorem certs109_22 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_22 = true := by
  decide +kernel

theorem certs109_23 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_23 = true := by
  decide +kernel

end Collatz
