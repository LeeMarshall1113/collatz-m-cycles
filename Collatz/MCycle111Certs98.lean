import Collatz.MCycle111Certs97

/-!
# Certificates of the listed shapes of `data111`, chunks 388..391
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_388 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_388 = true := by
  decide +kernel

theorem certs111_389 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_389 = true := by
  decide +kernel

theorem certs111_390 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_390 = true := by
  decide +kernel

theorem certs111_391 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_391 = true := by
  decide +kernel

end Collatz
