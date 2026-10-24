import Collatz.MCycle111Certs90

/-!
# Certificates of the listed shapes of `data111`, chunks 360..363
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_360 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_360 = true := by
  decide +kernel

theorem certs111_361 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_361 = true := by
  decide +kernel

theorem certs111_362 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_362 = true := by
  decide +kernel

theorem certs111_363 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_363 = true := by
  decide +kernel

end Collatz
