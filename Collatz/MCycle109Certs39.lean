import Collatz.MCycle109Certs38

/-!
# Certificates of the listed shapes of `data109`, chunks 152..155
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_152 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_152 = true := by
  decide +kernel

theorem certs109_153 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_153 = true := by
  decide +kernel

theorem certs109_154 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_154 = true := by
  decide +kernel

theorem certs109_155 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_155 = true := by
  decide +kernel

end Collatz
