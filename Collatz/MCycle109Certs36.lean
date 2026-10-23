import Collatz.MCycle109Certs35

/-!
# Certificates of the listed shapes of `data109`, chunks 140..143
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_140 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_140 = true := by
  decide +kernel

theorem certs109_141 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_141 = true := by
  decide +kernel

theorem certs109_142 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_142 = true := by
  decide +kernel

theorem certs109_143 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_143 = true := by
  decide +kernel

end Collatz
