import Collatz.MCycle111Certs141

/-!
# Certificates of the listed shapes of `data111`, chunks 564..567
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_564 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_564 = true := by
  decide +kernel

theorem certs111_565 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_565 = true := by
  decide +kernel

theorem certs111_566 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_566 = true := by
  decide +kernel

theorem certs111_567 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_567 = true := by
  decide +kernel

end Collatz
