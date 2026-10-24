import Collatz.MCycle111Certs167

/-!
# Certificates of the listed shapes of `data111`, chunks 668..671
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_668 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_668 = true := by
  decide +kernel

theorem certs111_669 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_669 = true := by
  decide +kernel

theorem certs111_670 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_670 = true := by
  decide +kernel

theorem certs111_671 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_671 = true := by
  decide +kernel

end Collatz
