import Collatz.MCycle111Certs134

/-!
# Certificates of the listed shapes of `data111`, chunks 536..539
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_536 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_536 = true := by
  decide +kernel

theorem certs111_537 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_537 = true := by
  decide +kernel

theorem certs111_538 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_538 = true := by
  decide +kernel

theorem certs111_539 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_539 = true := by
  decide +kernel

end Collatz
