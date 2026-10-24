import Collatz.MCycle111Certs32

/-!
# Certificates of the listed shapes of `data111`, chunks 128..131
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_128 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_128 = true := by
  decide +kernel

theorem certs111_129 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_129 = true := by
  decide +kernel

theorem certs111_130 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_130 = true := by
  decide +kernel

theorem certs111_131 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_131 = true := by
  decide +kernel

end Collatz
