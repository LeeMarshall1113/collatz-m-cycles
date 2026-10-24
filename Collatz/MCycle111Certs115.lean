import Collatz.MCycle111Certs114

/-!
# Certificates of the listed shapes of `data111`, chunks 456..459
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_456 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_456 = true := by
  decide +kernel

theorem certs111_457 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_457 = true := by
  decide +kernel

theorem certs111_458 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_458 = true := by
  decide +kernel

theorem certs111_459 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_459 = true := by
  decide +kernel

end Collatz
