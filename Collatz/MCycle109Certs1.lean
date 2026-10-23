import Collatz.MCycle109Shapes
import Collatz.MCycleGrid109
import Collatz.MCycleGrid3_107

/-!
# Certificates of the listed shapes of `data109`, chunks 0..3
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_0 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_0 = true := by
  decide +kernel

theorem certs109_1 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_1 = true := by
  decide +kernel

theorem certs109_2 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_2 = true := by
  decide +kernel

theorem certs109_3 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_3 = true := by
  decide +kernel

end Collatz
