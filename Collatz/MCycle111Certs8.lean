import Collatz.MCycle111Certs7

/-!
# Certificates of the listed shapes of `data111`, chunks 28..31
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_28 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_28 = true := by
  decide +kernel

theorem certs111_29 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_29 = true := by
  decide +kernel

theorem certs111_30 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_30 = true := by
  decide +kernel

theorem certs111_31 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_31 = true := by
  decide +kernel

end Collatz
