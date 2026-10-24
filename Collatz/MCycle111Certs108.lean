import Collatz.MCycle111Certs107

/-!
# Certificates of the listed shapes of `data111`, chunks 428..431
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_428 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_428 = true := by
  decide +kernel

theorem certs111_429 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_429 = true := by
  decide +kernel

theorem certs111_430 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_430 = true := by
  decide +kernel

theorem certs111_431 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_431 = true := by
  decide +kernel

end Collatz
