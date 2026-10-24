import Collatz.MCycle111Certs164

/-!
# Certificates of the listed shapes of `data111`, chunks 656..659
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_656 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_656 = true := by
  decide +kernel

theorem certs111_657 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_657 = true := by
  decide +kernel

theorem certs111_658 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_658 = true := by
  decide +kernel

theorem certs111_659 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_659 = true := by
  decide +kernel

end Collatz
