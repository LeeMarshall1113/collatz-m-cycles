import Collatz.MCycle111Certs91

/-!
# Certificates of the listed shapes of `data111`, chunks 364..367
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_364 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_364 = true := by
  decide +kernel

theorem certs111_365 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_365 = true := by
  decide +kernel

theorem certs111_366 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_366 = true := by
  decide +kernel

theorem certs111_367 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_367 = true := by
  decide +kernel

end Collatz
