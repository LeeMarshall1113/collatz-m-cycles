import Collatz.MCycle111Certs89

/-!
# Certificates of the listed shapes of `data111`, chunks 356..359
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_356 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_356 = true := by
  decide +kernel

theorem certs111_357 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_357 = true := by
  decide +kernel

theorem certs111_358 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_358 = true := by
  decide +kernel

theorem certs111_359 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_359 = true := by
  decide +kernel

end Collatz
