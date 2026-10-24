import Collatz.MCycle111Certs110

/-!
# Certificates of the listed shapes of `data111`, chunks 440..443
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_440 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_440 = true := by
  decide +kernel

theorem certs111_441 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_441 = true := by
  decide +kernel

theorem certs111_442 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_442 = true := by
  decide +kernel

theorem certs111_443 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_443 = true := by
  decide +kernel

end Collatz
