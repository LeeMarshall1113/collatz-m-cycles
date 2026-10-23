import Collatz.MCycle109Certs16

/-!
# Certificates of the listed shapes of `data109`, chunks 64..67
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_64 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_64 = true := by
  decide +kernel

theorem certs109_65 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_65 = true := by
  decide +kernel

theorem certs109_66 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_66 = true := by
  decide +kernel

theorem certs109_67 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_67 = true := by
  decide +kernel

end Collatz
