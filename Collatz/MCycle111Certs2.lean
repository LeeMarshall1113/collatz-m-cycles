import Collatz.MCycle111Certs1

/-!
# Certificates of the listed shapes of `data111`, chunks 4..7
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_4 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_4 = true := by
  decide +kernel

theorem certs111_5 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_5 = true := by
  decide +kernel

theorem certs111_6 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_6 = true := by
  decide +kernel

theorem certs111_7 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_7 = true := by
  decide +kernel

end Collatz
