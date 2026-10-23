import Collatz.MCycle109Certs7

/-!
# Certificates of the listed shapes of `data109`, chunks 28..31
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_28 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_28 = true := by
  decide +kernel

theorem certs109_29 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_29 = true := by
  decide +kernel

theorem certs109_30 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_30 = true := by
  decide +kernel

theorem certs109_31 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_31 = true := by
  decide +kernel

end Collatz
