import Collatz.MCycle111Certs100

/-!
# Certificates of the listed shapes of `data111`, chunks 400..403
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_400 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_400 = true := by
  decide +kernel

theorem certs111_401 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_401 = true := by
  decide +kernel

theorem certs111_402 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_402 = true := by
  decide +kernel

theorem certs111_403 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_403 = true := by
  decide +kernel

end Collatz
