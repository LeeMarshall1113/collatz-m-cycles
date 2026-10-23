import Collatz.MCycle109Certs10

/-!
# Certificates of the listed shapes of `data109`, chunks 40..43
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_40 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_40 = true := by
  decide +kernel

theorem certs109_41 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_41 = true := by
  decide +kernel

theorem certs109_42 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_42 = true := by
  decide +kernel

theorem certs109_43 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_43 = true := by
  decide +kernel

end Collatz
