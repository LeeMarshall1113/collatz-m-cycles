import Collatz.MCycle109Certs18

/-!
# Certificates of the listed shapes of `data109`, chunks 72..75
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_72 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_72 = true := by
  decide +kernel

theorem certs109_73 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_73 = true := by
  decide +kernel

theorem certs109_74 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_74 = true := by
  decide +kernel

theorem certs109_75 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_75 = true := by
  decide +kernel

end Collatz
