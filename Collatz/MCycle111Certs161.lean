import Collatz.MCycle111Certs160

/-!
# Certificates of the listed shapes of `data111`, chunks 640..643
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_640 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_640 = true := by
  decide +kernel

theorem certs111_641 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_641 = true := by
  decide +kernel

theorem certs111_642 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_642 = true := by
  decide +kernel

theorem certs111_643 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_643 = true := by
  decide +kernel

end Collatz
