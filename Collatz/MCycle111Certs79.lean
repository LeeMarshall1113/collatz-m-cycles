import Collatz.MCycle111Certs78

/-!
# Certificates of the listed shapes of `data111`, chunks 312..315
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_312 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_312 = true := by
  decide +kernel

theorem certs111_313 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_313 = true := by
  decide +kernel

theorem certs111_314 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_314 = true := by
  decide +kernel

theorem certs111_315 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_315 = true := by
  decide +kernel

end Collatz
