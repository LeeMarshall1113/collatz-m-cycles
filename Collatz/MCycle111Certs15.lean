import Collatz.MCycle111Certs14

/-!
# Certificates of the listed shapes of `data111`, chunks 56..59
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_56 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_56 = true := by
  decide +kernel

theorem certs111_57 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_57 = true := by
  decide +kernel

theorem certs111_58 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_58 = true := by
  decide +kernel

theorem certs111_59 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_59 = true := by
  decide +kernel

end Collatz
