import Collatz.MCycle111Certs108

/-!
# Certificates of the listed shapes of `data111`, chunks 432..435
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_432 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_432 = true := by
  decide +kernel

theorem certs111_433 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_433 = true := by
  decide +kernel

theorem certs111_434 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_434 = true := by
  decide +kernel

theorem certs111_435 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_435 = true := by
  decide +kernel

end Collatz
