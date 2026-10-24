import Collatz.MCycle111Certs95

/-!
# Certificates of the listed shapes of `data111`, chunks 380..383
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_380 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_380 = true := by
  decide +kernel

theorem certs111_381 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_381 = true := by
  decide +kernel

theorem certs111_382 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_382 = true := by
  decide +kernel

theorem certs111_383 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_383 = true := by
  decide +kernel

end Collatz
