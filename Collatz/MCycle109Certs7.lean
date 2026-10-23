import Collatz.MCycle109Certs6

/-!
# Certificates of the listed shapes of `data109`, chunks 24..27
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_24 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_24 = true := by
  decide +kernel

theorem certs109_25 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_25 = true := by
  decide +kernel

theorem certs109_26 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_26 = true := by
  decide +kernel

theorem certs109_27 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_27 = true := by
  decide +kernel

end Collatz
