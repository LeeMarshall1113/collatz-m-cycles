import Collatz.MCycle111Certs77

/-!
# Certificates of the listed shapes of `data111`, chunks 308..311
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_308 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_308 = true := by
  decide +kernel

theorem certs111_309 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_309 = true := by
  decide +kernel

theorem certs111_310 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_310 = true := by
  decide +kernel

theorem certs111_311 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_311 = true := by
  decide +kernel

end Collatz
