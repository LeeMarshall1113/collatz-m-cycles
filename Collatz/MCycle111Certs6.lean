import Collatz.MCycle111Certs5

/-!
# Certificates of the listed shapes of `data111`, chunks 20..23
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_20 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_20 = true := by
  decide +kernel

theorem certs111_21 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_21 = true := by
  decide +kernel

theorem certs111_22 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_22 = true := by
  decide +kernel

theorem certs111_23 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_23 = true := by
  decide +kernel

end Collatz
