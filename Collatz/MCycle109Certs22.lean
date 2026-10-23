import Collatz.MCycle109Certs21

/-!
# Certificates of the listed shapes of `data109`, chunks 84..87
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_84 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_84 = true := by
  decide +kernel

theorem certs109_85 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_85 = true := by
  decide +kernel

theorem certs109_86 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_86 = true := by
  decide +kernel

theorem certs109_87 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_87 = true := by
  decide +kernel

end Collatz
