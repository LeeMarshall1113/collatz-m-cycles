import Collatz.MCycle111Certs145

/-!
# Certificates of the listed shapes of `data111`, chunks 580..583
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_580 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_580 = true := by
  decide +kernel

theorem certs111_581 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_581 = true := by
  decide +kernel

theorem certs111_582 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_582 = true := by
  decide +kernel

theorem certs111_583 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_583 = true := by
  decide +kernel

end Collatz
