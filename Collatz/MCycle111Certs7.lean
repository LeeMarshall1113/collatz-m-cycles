import Collatz.MCycle111Certs6

/-!
# Certificates of the listed shapes of `data111`, chunks 24..27
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_24 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_24 = true := by
  decide +kernel

theorem certs111_25 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_25 = true := by
  decide +kernel

theorem certs111_26 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_26 = true := by
  decide +kernel

theorem certs111_27 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_27 = true := by
  decide +kernel

end Collatz
