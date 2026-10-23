import Collatz.MCycle109Certs3

/-!
# Certificates of the listed shapes of `data109`, chunks 12..15
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_12 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_12 = true := by
  decide +kernel

theorem certs109_13 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_13 = true := by
  decide +kernel

theorem certs109_14 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_14 = true := by
  decide +kernel

theorem certs109_15 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_15 = true := by
  decide +kernel

end Collatz
