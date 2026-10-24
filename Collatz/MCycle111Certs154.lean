import Collatz.MCycle111Certs153

/-!
# Certificates of the listed shapes of `data111`, chunks 612..615
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_612 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_612 = true := by
  decide +kernel

theorem certs111_613 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_613 = true := by
  decide +kernel

theorem certs111_614 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_614 = true := by
  decide +kernel

theorem certs111_615 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_615 = true := by
  decide +kernel

end Collatz
