import Collatz.MCycle111Certs71

/-!
# Certificates of the listed shapes of `data111`, chunks 284..287
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_284 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_284 = true := by
  decide +kernel

theorem certs111_285 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_285 = true := by
  decide +kernel

theorem certs111_286 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_286 = true := by
  decide +kernel

theorem certs111_287 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_287 = true := by
  decide +kernel

end Collatz
