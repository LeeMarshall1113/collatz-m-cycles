import Collatz.MCycle111Certs150

/-!
# Certificates of the listed shapes of `data111`, chunks 600..603
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_600 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_600 = true := by
  decide +kernel

theorem certs111_601 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_601 = true := by
  decide +kernel

theorem certs111_602 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_602 = true := by
  decide +kernel

theorem certs111_603 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_603 = true := by
  decide +kernel

end Collatz
