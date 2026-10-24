import Collatz.MCycle111Certs130

/-!
# Certificates of the listed shapes of `data111`, chunks 520..523
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_520 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_520 = true := by
  decide +kernel

theorem certs111_521 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_521 = true := by
  decide +kernel

theorem certs111_522 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_522 = true := by
  decide +kernel

theorem certs111_523 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_523 = true := by
  decide +kernel

end Collatz
