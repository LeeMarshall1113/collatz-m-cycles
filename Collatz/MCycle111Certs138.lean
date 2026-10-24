import Collatz.MCycle111Certs137

/-!
# Certificates of the listed shapes of `data111`, chunks 548..551
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_548 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_548 = true := by
  decide +kernel

theorem certs111_549 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_549 = true := by
  decide +kernel

theorem certs111_550 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_550 = true := by
  decide +kernel

theorem certs111_551 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_551 = true := by
  decide +kernel

end Collatz
