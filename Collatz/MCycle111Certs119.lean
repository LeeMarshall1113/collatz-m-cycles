import Collatz.MCycle111Certs118

/-!
# Certificates of the listed shapes of `data111`, chunks 472..475
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_472 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_472 = true := by
  decide +kernel

theorem certs111_473 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_473 = true := by
  decide +kernel

theorem certs111_474 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_474 = true := by
  decide +kernel

theorem certs111_475 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_475 = true := by
  decide +kernel

end Collatz
