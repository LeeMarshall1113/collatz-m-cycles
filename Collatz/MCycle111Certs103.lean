import Collatz.MCycle111Certs102

/-!
# Certificates of the listed shapes of `data111`, chunks 408..411
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_408 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_408 = true := by
  decide +kernel

theorem certs111_409 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_409 = true := by
  decide +kernel

theorem certs111_410 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_410 = true := by
  decide +kernel

theorem certs111_411 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_411 = true := by
  decide +kernel

end Collatz
