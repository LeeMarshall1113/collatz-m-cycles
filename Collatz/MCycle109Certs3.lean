import Collatz.MCycle109Certs2

/-!
# Certificates of the listed shapes of `data109`, chunks 8..11
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_8 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_8 = true := by
  decide +kernel

theorem certs109_9 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_9 = true := by
  decide +kernel

theorem certs109_10 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_10 = true := by
  decide +kernel

theorem certs109_11 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_11 = true := by
  decide +kernel

end Collatz
