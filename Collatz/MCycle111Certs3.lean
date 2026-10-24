import Collatz.MCycle111Certs2

/-!
# Certificates of the listed shapes of `data111`, chunks 8..11
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_8 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_8 = true := by
  decide +kernel

theorem certs111_9 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_9 = true := by
  decide +kernel

theorem certs111_10 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_10 = true := by
  decide +kernel

theorem certs111_11 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_11 = true := by
  decide +kernel

end Collatz
