import Collatz.MCycle111Certs138

/-!
# Certificates of the listed shapes of `data111`, chunks 552..555
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_552 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_552 = true := by
  decide +kernel

theorem certs111_553 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_553 = true := by
  decide +kernel

theorem certs111_554 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_554 = true := by
  decide +kernel

theorem certs111_555 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_555 = true := by
  decide +kernel

end Collatz
