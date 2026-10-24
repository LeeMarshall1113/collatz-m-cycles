import Collatz.MCycle111Certs39

/-!
# Certificates of the listed shapes of `data111`, chunks 156..159
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_156 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_156 = true := by
  decide +kernel

theorem certs111_157 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_157 = true := by
  decide +kernel

theorem certs111_158 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_158 = true := by
  decide +kernel

theorem certs111_159 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_159 = true := by
  decide +kernel

end Collatz
