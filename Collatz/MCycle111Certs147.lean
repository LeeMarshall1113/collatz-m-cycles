import Collatz.MCycle111Certs146

/-!
# Certificates of the listed shapes of `data111`, chunks 584..587
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_584 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_584 = true := by
  decide +kernel

theorem certs111_585 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_585 = true := by
  decide +kernel

theorem certs111_586 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_586 = true := by
  decide +kernel

theorem certs111_587 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_587 = true := by
  decide +kernel

end Collatz
