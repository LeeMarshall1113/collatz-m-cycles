import Collatz.MCycle104Shapes
import Collatz.MCycleGrid103
import Collatz.MCycleGrid3_105

/-!
# Certificates of the listed shapes of `data104`, chunks 0..3
-/

set_option Elab.async false

namespace Collatz

theorem certs104_0 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_0 = true := by
  decide +kernel

theorem certs104_1 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_1 = true := by
  decide +kernel

theorem certs104_2 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_2 = true := by
  decide +kernel

theorem certs104_3 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_3 = true := by
  decide +kernel

end Collatz
