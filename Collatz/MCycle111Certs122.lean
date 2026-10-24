import Collatz.MCycle111Certs121

/-!
# Certificates of the listed shapes of `data111`, chunks 484..487
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_484 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_484 = true := by
  decide +kernel

theorem certs111_485 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_485 = true := by
  decide +kernel

theorem certs111_486 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_486 = true := by
  decide +kernel

theorem certs111_487 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_487 = true := by
  decide +kernel

end Collatz
