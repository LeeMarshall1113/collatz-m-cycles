import Collatz.MCycle111Certs8

/-!
# Certificates of the listed shapes of `data111`, chunks 32..35
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_32 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_32 = true := by
  decide +kernel

theorem certs111_33 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_33 = true := by
  decide +kernel

theorem certs111_34 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_34 = true := by
  decide +kernel

theorem certs111_35 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_35 = true := by
  decide +kernel

end Collatz
