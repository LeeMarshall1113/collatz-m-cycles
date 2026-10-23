import Collatz.MCycle109Certs4

/-!
# Certificates of the listed shapes of `data109`, chunks 16..19
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_16 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_16 = true := by
  decide +kernel

theorem certs109_17 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_17 = true := by
  decide +kernel

theorem certs109_18 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_18 = true := by
  decide +kernel

theorem certs109_19 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_19 = true := by
  decide +kernel

end Collatz
