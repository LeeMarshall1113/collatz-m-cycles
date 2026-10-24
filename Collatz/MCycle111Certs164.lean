import Collatz.MCycle111Certs163

/-!
# Certificates of the listed shapes of `data111`, chunks 652..655
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_652 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_652 = true := by
  decide +kernel

theorem certs111_653 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_653 = true := by
  decide +kernel

theorem certs111_654 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_654 = true := by
  decide +kernel

theorem certs111_655 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_655 = true := by
  decide +kernel

end Collatz
