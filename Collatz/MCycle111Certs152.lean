import Collatz.MCycle111Certs151

/-!
# Certificates of the listed shapes of `data111`, chunks 604..607
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_604 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_604 = true := by
  decide +kernel

theorem certs111_605 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_605 = true := by
  decide +kernel

theorem certs111_606 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_606 = true := by
  decide +kernel

theorem certs111_607 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_607 = true := by
  decide +kernel

end Collatz
