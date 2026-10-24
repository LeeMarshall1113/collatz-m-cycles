import Collatz.MCycle111Certs113

/-!
# Certificates of the listed shapes of `data111`, chunks 452..455
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_452 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_452 = true := by
  decide +kernel

theorem certs111_453 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_453 = true := by
  decide +kernel

theorem certs111_454 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_454 = true := by
  decide +kernel

theorem certs111_455 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_455 = true := by
  decide +kernel

end Collatz
