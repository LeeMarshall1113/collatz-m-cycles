import Collatz.MCycle111Certs87

/-!
# Certificates of the listed shapes of `data111`, chunks 348..351
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_348 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_348 = true := by
  decide +kernel

theorem certs111_349 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_349 = true := by
  decide +kernel

theorem certs111_350 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_350 = true := by
  decide +kernel

theorem certs111_351 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_351 = true := by
  decide +kernel

end Collatz
