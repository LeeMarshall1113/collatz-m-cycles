import Collatz.MCycle111Certs25

/-!
# Certificates of the listed shapes of `data111`, chunks 100..103
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_100 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_100 = true := by
  decide +kernel

theorem certs111_101 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_101 = true := by
  decide +kernel

theorem certs111_102 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_102 = true := by
  decide +kernel

theorem certs111_103 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_103 = true := by
  decide +kernel

end Collatz
