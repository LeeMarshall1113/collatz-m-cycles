import Collatz.MCycle111Certs133

/-!
# Certificates of the listed shapes of `data111`, chunks 532..535
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_532 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_532 = true := by
  decide +kernel

theorem certs111_533 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_533 = true := by
  decide +kernel

theorem certs111_534 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_534 = true := by
  decide +kernel

theorem certs111_535 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_535 = true := by
  decide +kernel

end Collatz
