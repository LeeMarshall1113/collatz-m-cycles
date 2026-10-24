import Collatz.MCycle111Certs155

/-!
# Certificates of the listed shapes of `data111`, chunks 620..623
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_620 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_620 = true := by
  decide +kernel

theorem certs111_621 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_621 = true := by
  decide +kernel

theorem certs111_622 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_622 = true := by
  decide +kernel

theorem certs111_623 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_623 = true := by
  decide +kernel

end Collatz
