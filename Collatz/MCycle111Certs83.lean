import Collatz.MCycle111Certs82

/-!
# Certificates of the listed shapes of `data111`, chunks 328..331
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_328 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_328 = true := by
  decide +kernel

theorem certs111_329 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_329 = true := by
  decide +kernel

theorem certs111_330 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_330 = true := by
  decide +kernel

theorem certs111_331 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_331 = true := by
  decide +kernel

end Collatz
