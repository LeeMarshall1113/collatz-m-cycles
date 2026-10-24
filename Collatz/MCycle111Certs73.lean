import Collatz.MCycle111Certs72

/-!
# Certificates of the listed shapes of `data111`, chunks 288..291
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_288 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_288 = true := by
  decide +kernel

theorem certs111_289 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_289 = true := by
  decide +kernel

theorem certs111_290 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_290 = true := by
  decide +kernel

theorem certs111_291 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_291 = true := by
  decide +kernel

end Collatz
