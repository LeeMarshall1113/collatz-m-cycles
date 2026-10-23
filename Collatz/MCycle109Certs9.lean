import Collatz.MCycle109Certs8

/-!
# Certificates of the listed shapes of `data109`, chunks 32..35
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_32 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_32 = true := by
  decide +kernel

theorem certs109_33 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_33 = true := by
  decide +kernel

theorem certs109_34 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_34 = true := by
  decide +kernel

theorem certs109_35 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_35 = true := by
  decide +kernel

end Collatz
