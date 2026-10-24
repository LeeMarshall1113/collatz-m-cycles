import Collatz.MCycle111Certs147

/-!
# Certificates of the listed shapes of `data111`, chunks 588..591
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_588 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_588 = true := by
  decide +kernel

theorem certs111_589 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_589 = true := by
  decide +kernel

theorem certs111_590 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_590 = true := by
  decide +kernel

theorem certs111_591 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_591 = true := by
  decide +kernel

end Collatz
