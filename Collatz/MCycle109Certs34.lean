import Collatz.MCycle109Certs33

/-!
# Certificates of the listed shapes of `data109`, chunks 132..135
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_132 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_132 = true := by
  decide +kernel

theorem certs109_133 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_133 = true := by
  decide +kernel

theorem certs109_134 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_134 = true := by
  decide +kernel

theorem certs109_135 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_135 = true := by
  decide +kernel

end Collatz
