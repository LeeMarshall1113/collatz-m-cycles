import Collatz.MCycle111Certs131

/-!
# Certificates of the listed shapes of `data111`, chunks 524..527
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_524 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_524 = true := by
  decide +kernel

theorem certs111_525 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_525 = true := by
  decide +kernel

theorem certs111_526 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_526 = true := by
  decide +kernel

theorem certs111_527 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_527 = true := by
  decide +kernel

end Collatz
