import Collatz.MCycle111Certs66

/-!
# Certificates of the listed shapes of `data111`, chunks 264..267
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_264 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_264 = true := by
  decide +kernel

theorem certs111_265 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_265 = true := by
  decide +kernel

theorem certs111_266 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_266 = true := by
  decide +kernel

theorem certs111_267 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_267 = true := by
  decide +kernel

end Collatz
