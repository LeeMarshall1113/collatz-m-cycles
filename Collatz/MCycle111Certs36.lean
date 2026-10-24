import Collatz.MCycle111Certs35

/-!
# Certificates of the listed shapes of `data111`, chunks 140..143
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_140 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_140 = true := by
  decide +kernel

theorem certs111_141 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_141 = true := by
  decide +kernel

theorem certs111_142 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_142 = true := by
  decide +kernel

theorem certs111_143 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_143 = true := by
  decide +kernel

end Collatz
