import Collatz.MCycle111Certs117

/-!
# Certificates of the listed shapes of `data111`, chunks 468..471
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_468 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_468 = true := by
  decide +kernel

theorem certs111_469 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_469 = true := by
  decide +kernel

theorem certs111_470 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_470 = true := by
  decide +kernel

theorem certs111_471 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_471 = true := by
  decide +kernel

end Collatz
