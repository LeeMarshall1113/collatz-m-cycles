import Collatz.MCycle111Certs3

/-!
# Certificates of the listed shapes of `data111`, chunks 12..15
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_12 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_12 = true := by
  decide +kernel

theorem certs111_13 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_13 = true := by
  decide +kernel

theorem certs111_14 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_14 = true := by
  decide +kernel

theorem certs111_15 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_15 = true := by
  decide +kernel

end Collatz
