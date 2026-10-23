import Collatz.MCycle109Certs14

/-!
# Certificates of the listed shapes of `data109`, chunks 56..59
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_56 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_56 = true := by
  decide +kernel

theorem certs109_57 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_57 = true := by
  decide +kernel

theorem certs109_58 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_58 = true := by
  decide +kernel

theorem certs109_59 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_59 = true := by
  decide +kernel

end Collatz
