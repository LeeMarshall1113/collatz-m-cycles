import Collatz.MCycle111Certs124

/-!
# Certificates of the listed shapes of `data111`, chunks 496..499
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_496 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_496 = true := by
  decide +kernel

theorem certs111_497 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_497 = true := by
  decide +kernel

theorem certs111_498 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_498 = true := by
  decide +kernel

theorem certs111_499 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_499 = true := by
  decide +kernel

end Collatz
