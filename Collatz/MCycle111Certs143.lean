import Collatz.MCycle111Certs142

/-!
# Certificates of the listed shapes of `data111`, chunks 568..571
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_568 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_568 = true := by
  decide +kernel

theorem certs111_569 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_569 = true := by
  decide +kernel

theorem certs111_570 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_570 = true := by
  decide +kernel

theorem certs111_571 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_571 = true := by
  decide +kernel

end Collatz
