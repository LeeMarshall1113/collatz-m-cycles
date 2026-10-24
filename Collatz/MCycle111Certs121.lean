import Collatz.MCycle111Certs120

/-!
# Certificates of the listed shapes of `data111`, chunks 480..483
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_480 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_480 = true := by
  decide +kernel

theorem certs111_481 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_481 = true := by
  decide +kernel

theorem certs111_482 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_482 = true := by
  decide +kernel

theorem certs111_483 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_483 = true := by
  decide +kernel

end Collatz
