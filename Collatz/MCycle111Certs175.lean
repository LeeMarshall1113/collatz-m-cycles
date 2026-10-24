import Collatz.MCycle111Certs174

/-!
# Certificates of the listed shapes of `data111`, chunks 696..699
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_696 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_696 = true := by
  decide +kernel

theorem certs111_697 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_697 = true := by
  decide +kernel

theorem certs111_698 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_698 = true := by
  decide +kernel

theorem certs111_699 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_699 = true := by
  decide +kernel

end Collatz
