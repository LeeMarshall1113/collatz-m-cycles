import Collatz.MCycle111Certs59

/-!
# Certificates of the listed shapes of `data111`, chunks 236..239
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_236 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_236 = true := by
  decide +kernel

theorem certs111_237 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_237 = true := by
  decide +kernel

theorem certs111_238 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_238 = true := by
  decide +kernel

theorem certs111_239 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_239 = true := by
  decide +kernel

end Collatz
