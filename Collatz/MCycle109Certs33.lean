import Collatz.MCycle109Certs32

/-!
# Certificates of the listed shapes of `data109`, chunks 128..131
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_128 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_128 = true := by
  decide +kernel

theorem certs109_129 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_129 = true := by
  decide +kernel

theorem certs109_130 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_130 = true := by
  decide +kernel

theorem certs109_131 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_131 = true := by
  decide +kernel

end Collatz
