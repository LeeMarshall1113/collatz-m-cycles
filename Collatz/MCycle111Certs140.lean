import Collatz.MCycle111Certs139

/-!
# Certificates of the listed shapes of `data111`, chunks 556..559
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_556 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_556 = true := by
  decide +kernel

theorem certs111_557 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_557 = true := by
  decide +kernel

theorem certs111_558 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_558 = true := by
  decide +kernel

theorem certs111_559 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_559 = true := by
  decide +kernel

end Collatz
