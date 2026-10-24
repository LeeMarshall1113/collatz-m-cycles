import Collatz.MCycle111Certs31

/-!
# Certificates of the listed shapes of `data111`, chunks 124..127
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_124 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_124 = true := by
  decide +kernel

theorem certs111_125 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_125 = true := by
  decide +kernel

theorem certs111_126 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_126 = true := by
  decide +kernel

theorem certs111_127 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_127 = true := by
  decide +kernel

end Collatz
