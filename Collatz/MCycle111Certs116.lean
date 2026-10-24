import Collatz.MCycle111Certs115

/-!
# Certificates of the listed shapes of `data111`, chunks 460..463
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_460 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_460 = true := by
  decide +kernel

theorem certs111_461 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_461 = true := by
  decide +kernel

theorem certs111_462 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_462 = true := by
  decide +kernel

theorem certs111_463 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_463 = true := by
  decide +kernel

end Collatz
