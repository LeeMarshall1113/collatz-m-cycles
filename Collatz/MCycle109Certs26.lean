import Collatz.MCycle109Certs25

/-!
# Certificates of the listed shapes of `data109`, chunks 100..103
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_100 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_100 = true := by
  decide +kernel

theorem certs109_101 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_101 = true := by
  decide +kernel

theorem certs109_102 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_102 = true := by
  decide +kernel

theorem certs109_103 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_103 = true := by
  decide +kernel

end Collatz
