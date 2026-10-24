import Collatz.MCycle111Shapes
import Collatz.MCycleGrid111
import Collatz.MCycleGrid3_111

/-!
# Certificates of the listed shapes of `data111`, chunks 0..3
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_0 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_0 = true := by
  decide +kernel

theorem certs111_1 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_1 = true := by
  decide +kernel

theorem certs111_2 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_2 = true := by
  decide +kernel

theorem certs111_3 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_3 = true := by
  decide +kernel

end Collatz
