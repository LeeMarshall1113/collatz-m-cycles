import Collatz.MCycle109Certs17

/-!
# Certificates of the listed shapes of `data109`, chunks 68..71
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_68 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_68 = true := by
  decide +kernel

theorem certs109_69 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_69 = true := by
  decide +kernel

theorem certs109_70 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_70 = true := by
  decide +kernel

theorem certs109_71 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_71 = true := by
  decide +kernel

end Collatz
