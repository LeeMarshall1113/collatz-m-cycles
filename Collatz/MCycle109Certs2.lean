import Collatz.MCycle109Certs1

/-!
# Certificates of the listed shapes of `data109`, chunks 4..7
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_4 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_4 = true := by
  decide +kernel

theorem certs109_5 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_5 = true := by
  decide +kernel

theorem certs109_6 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_6 = true := by
  decide +kernel

theorem certs109_7 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_7 = true := by
  decide +kernel

end Collatz
