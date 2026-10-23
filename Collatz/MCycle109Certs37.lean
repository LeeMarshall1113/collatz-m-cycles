import Collatz.MCycle109Certs36

/-!
# Certificates of the listed shapes of `data109`, chunks 144..147
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_144 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_144 = true := by
  decide +kernel

theorem certs109_145 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_145 = true := by
  decide +kernel

theorem certs109_146 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_146 = true := by
  decide +kernel

theorem certs109_147 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_147 = true := by
  decide +kernel

end Collatz
