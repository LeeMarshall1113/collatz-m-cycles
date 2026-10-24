import Collatz.MCycle111Certs123

/-!
# Certificates of the listed shapes of `data111`, chunks 492..495
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_492 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_492 = true := by
  decide +kernel

theorem certs111_493 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_493 = true := by
  decide +kernel

theorem certs111_494 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_494 = true := by
  decide +kernel

theorem certs111_495 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_495 = true := by
  decide +kernel

end Collatz
