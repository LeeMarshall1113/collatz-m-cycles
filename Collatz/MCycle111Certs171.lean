import Collatz.MCycle111Certs170

/-!
# Certificates of the listed shapes of `data111`, chunks 680..683
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_680 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_680 = true := by
  decide +kernel

theorem certs111_681 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_681 = true := by
  decide +kernel

theorem certs111_682 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_682 = true := by
  decide +kernel

theorem certs111_683 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_683 = true := by
  decide +kernel

end Collatz
