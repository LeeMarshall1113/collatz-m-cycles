import Collatz.MCycle109Certs28

/-!
# Certificates of the listed shapes of `data109`, chunks 112..115
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_112 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_112 = true := by
  decide +kernel

theorem certs109_113 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_113 = true := by
  decide +kernel

theorem certs109_114 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_114 = true := by
  decide +kernel

theorem certs109_115 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_115 = true := by
  decide +kernel

end Collatz
