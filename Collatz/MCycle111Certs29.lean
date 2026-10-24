import Collatz.MCycle111Certs28

/-!
# Certificates of the listed shapes of `data111`, chunks 112..115
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_112 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_112 = true := by
  decide +kernel

theorem certs111_113 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_113 = true := by
  decide +kernel

theorem certs111_114 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_114 = true := by
  decide +kernel

theorem certs111_115 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_115 = true := by
  decide +kernel

end Collatz
