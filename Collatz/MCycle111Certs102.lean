import Collatz.MCycle111Certs101

/-!
# Certificates of the listed shapes of `data111`, chunks 404..407
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_404 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_404 = true := by
  decide +kernel

theorem certs111_405 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_405 = true := by
  decide +kernel

theorem certs111_406 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_406 = true := by
  decide +kernel

theorem certs111_407 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_407 = true := by
  decide +kernel

end Collatz
