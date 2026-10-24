import Collatz.MCycle111Certs103

/-!
# Certificates of the listed shapes of `data111`, chunks 412..415
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_412 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_412 = true := by
  decide +kernel

theorem certs111_413 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_413 = true := by
  decide +kernel

theorem certs111_414 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_414 = true := by
  decide +kernel

theorem certs111_415 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_415 = true := by
  decide +kernel

end Collatz
