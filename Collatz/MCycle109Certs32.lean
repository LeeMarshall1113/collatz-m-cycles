import Collatz.MCycle109Certs31

/-!
# Certificates of the listed shapes of `data109`, chunks 124..127
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_124 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_124 = true := by
  decide +kernel

theorem certs109_125 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_125 = true := by
  decide +kernel

theorem certs109_126 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_126 = true := by
  decide +kernel

theorem certs109_127 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_127 = true := by
  decide +kernel

end Collatz
