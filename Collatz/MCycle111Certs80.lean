import Collatz.MCycle111Certs79

/-!
# Certificates of the listed shapes of `data111`, chunks 316..319
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_316 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_316 = true := by
  decide +kernel

theorem certs111_317 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_317 = true := by
  decide +kernel

theorem certs111_318 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_318 = true := by
  decide +kernel

theorem certs111_319 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_319 = true := by
  decide +kernel

end Collatz
