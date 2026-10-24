import Collatz.MCycle111Certs116

/-!
# Certificates of the listed shapes of `data111`, chunks 464..467
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_464 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_464 = true := by
  decide +kernel

theorem certs111_465 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_465 = true := by
  decide +kernel

theorem certs111_466 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_466 = true := by
  decide +kernel

theorem certs111_467 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_467 = true := by
  decide +kernel

end Collatz
