import Collatz.MCycle111Certs68

/-!
# Certificates of the listed shapes of `data111`, chunks 272..275
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_272 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_272 = true := by
  decide +kernel

theorem certs111_273 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_273 = true := by
  decide +kernel

theorem certs111_274 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_274 = true := by
  decide +kernel

theorem certs111_275 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_275 = true := by
  decide +kernel

end Collatz
