import Collatz.MCycle111Certs50

/-!
# Certificates of the listed shapes of `data111`, chunks 200..203
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_200 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_200 = true := by
  decide +kernel

theorem certs111_201 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_201 = true := by
  decide +kernel

theorem certs111_202 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_202 = true := by
  decide +kernel

theorem certs111_203 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_203 = true := by
  decide +kernel

end Collatz
