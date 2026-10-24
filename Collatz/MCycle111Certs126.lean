import Collatz.MCycle111Certs125

/-!
# Certificates of the listed shapes of `data111`, chunks 500..503
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_500 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_500 = true := by
  decide +kernel

theorem certs111_501 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_501 = true := by
  decide +kernel

theorem certs111_502 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_502 = true := by
  decide +kernel

theorem certs111_503 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_503 = true := by
  decide +kernel

end Collatz
