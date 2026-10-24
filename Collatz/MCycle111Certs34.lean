import Collatz.MCycle111Certs33

/-!
# Certificates of the listed shapes of `data111`, chunks 132..135
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_132 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_132 = true := by
  decide +kernel

theorem certs111_133 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_133 = true := by
  decide +kernel

theorem certs111_134 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_134 = true := by
  decide +kernel

theorem certs111_135 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_135 = true := by
  decide +kernel

end Collatz
