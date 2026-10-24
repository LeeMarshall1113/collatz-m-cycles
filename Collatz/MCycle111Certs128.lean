import Collatz.MCycle111Certs127

/-!
# Certificates of the listed shapes of `data111`, chunks 508..511
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_508 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_508 = true := by
  decide +kernel

theorem certs111_509 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_509 = true := by
  decide +kernel

theorem certs111_510 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_510 = true := by
  decide +kernel

theorem certs111_511 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_511 = true := by
  decide +kernel

end Collatz
