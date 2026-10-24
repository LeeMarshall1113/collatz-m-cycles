import Collatz.MCycle111Certs119

/-!
# Certificates of the listed shapes of `data111`, chunks 476..479
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_476 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_476 = true := by
  decide +kernel

theorem certs111_477 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_477 = true := by
  decide +kernel

theorem certs111_478 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_478 = true := by
  decide +kernel

theorem certs111_479 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_479 = true := by
  decide +kernel

end Collatz
