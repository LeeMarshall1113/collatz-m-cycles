import Collatz.MCycle109Certs24

/-!
# Certificates of the listed shapes of `data109`, chunks 96..99
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_96 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_96 = true := by
  decide +kernel

theorem certs109_97 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_97 = true := by
  decide +kernel

theorem certs109_98 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_98 = true := by
  decide +kernel

theorem certs109_99 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_99 = true := by
  decide +kernel

end Collatz
