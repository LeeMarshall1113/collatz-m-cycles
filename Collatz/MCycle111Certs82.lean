import Collatz.MCycle111Certs81

/-!
# Certificates of the listed shapes of `data111`, chunks 324..327
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_324 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_324 = true := by
  decide +kernel

theorem certs111_325 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_325 = true := by
  decide +kernel

theorem certs111_326 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_326 = true := by
  decide +kernel

theorem certs111_327 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_327 = true := by
  decide +kernel

end Collatz
