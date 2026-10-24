import Collatz.MCycle111Certs175

/-!
# Certificates of the listed shapes of `data111`, chunks 700..703
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_700 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_700 = true := by
  decide +kernel

theorem certs111_701 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_701 = true := by
  decide +kernel

theorem certs111_702 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_702 = true := by
  decide +kernel

theorem certs111_703 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_703 = true := by
  decide +kernel

end Collatz
