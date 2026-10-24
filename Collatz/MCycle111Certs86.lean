import Collatz.MCycle111Certs85

/-!
# Certificates of the listed shapes of `data111`, chunks 340..343
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_340 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_340 = true := by
  decide +kernel

theorem certs111_341 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_341 = true := by
  decide +kernel

theorem certs111_342 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_342 = true := by
  decide +kernel

theorem certs111_343 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_343 = true := by
  decide +kernel

end Collatz
