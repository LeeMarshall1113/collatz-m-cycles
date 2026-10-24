import Collatz.MCycle111Certs65

/-!
# Certificates of the listed shapes of `data111`, chunks 260..263
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_260 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_260 = true := by
  decide +kernel

theorem certs111_261 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_261 = true := by
  decide +kernel

theorem certs111_262 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_262 = true := by
  decide +kernel

theorem certs111_263 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_263 = true := by
  decide +kernel

end Collatz
