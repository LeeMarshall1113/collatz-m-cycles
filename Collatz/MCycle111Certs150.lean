import Collatz.MCycle111Certs149

/-!
# Certificates of the listed shapes of `data111`, chunks 596..599
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_596 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_596 = true := by
  decide +kernel

theorem certs111_597 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_597 = true := by
  decide +kernel

theorem certs111_598 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_598 = true := by
  decide +kernel

theorem certs111_599 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_599 = true := by
  decide +kernel

end Collatz
