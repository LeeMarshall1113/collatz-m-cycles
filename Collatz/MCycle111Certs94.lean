import Collatz.MCycle111Certs93

/-!
# Certificates of the listed shapes of `data111`, chunks 372..375
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_372 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_372 = true := by
  decide +kernel

theorem certs111_373 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_373 = true := by
  decide +kernel

theorem certs111_374 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_374 = true := by
  decide +kernel

theorem certs111_375 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_375 = true := by
  decide +kernel

end Collatz
