import Collatz.MCycle111Certs173

/-!
# Certificates of the listed shapes of `data111`, chunks 692..695
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_692 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_692 = true := by
  decide +kernel

theorem certs111_693 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_693 = true := by
  decide +kernel

theorem certs111_694 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_694 = true := by
  decide +kernel

theorem certs111_695 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_695 = true := by
  decide +kernel

end Collatz
