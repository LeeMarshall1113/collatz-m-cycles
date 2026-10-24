import Collatz.MCycle111Certs112

/-!
# Certificates of the listed shapes of `data111`, chunks 448..451
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_448 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_448 = true := by
  decide +kernel

theorem certs111_449 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_449 = true := by
  decide +kernel

theorem certs111_450 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_450 = true := by
  decide +kernel

theorem certs111_451 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_451 = true := by
  decide +kernel

end Collatz
