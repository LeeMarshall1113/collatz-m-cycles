import Collatz.MCycle111Certs80

/-!
# Certificates of the listed shapes of `data111`, chunks 320..323
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_320 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_320 = true := by
  decide +kernel

theorem certs111_321 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_321 = true := by
  decide +kernel

theorem certs111_322 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_322 = true := by
  decide +kernel

theorem certs111_323 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_323 = true := by
  decide +kernel

end Collatz
