import Collatz.MCycle111Certs148

/-!
# Certificates of the listed shapes of `data111`, chunks 592..595
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_592 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_592 = true := by
  decide +kernel

theorem certs111_593 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_593 = true := by
  decide +kernel

theorem certs111_594 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_594 = true := by
  decide +kernel

theorem certs111_595 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_595 = true := by
  decide +kernel

end Collatz
