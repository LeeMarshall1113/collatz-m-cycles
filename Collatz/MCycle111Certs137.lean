import Collatz.MCycle111Certs136

/-!
# Certificates of the listed shapes of `data111`, chunks 544..547
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_544 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_544 = true := by
  decide +kernel

theorem certs111_545 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_545 = true := by
  decide +kernel

theorem certs111_546 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_546 = true := by
  decide +kernel

theorem certs111_547 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_547 = true := by
  decide +kernel

end Collatz
