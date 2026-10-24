import Collatz.MCycle111Certs166

/-!
# Certificates of the listed shapes of `data111`, chunks 664..667
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_664 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_664 = true := by
  decide +kernel

theorem certs111_665 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_665 = true := by
  decide +kernel

theorem certs111_666 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_666 = true := by
  decide +kernel

theorem certs111_667 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_667 = true := by
  decide +kernel

end Collatz
