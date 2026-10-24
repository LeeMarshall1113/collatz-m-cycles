import Collatz.MCycle111Certs105

/-!
# Certificates of the listed shapes of `data111`, chunks 420..423
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_420 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_420 = true := by
  decide +kernel

theorem certs111_421 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_421 = true := by
  decide +kernel

theorem certs111_422 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_422 = true := by
  decide +kernel

theorem certs111_423 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_423 = true := by
  decide +kernel

end Collatz
