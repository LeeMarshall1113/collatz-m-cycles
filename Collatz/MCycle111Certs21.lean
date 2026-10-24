import Collatz.MCycle111Certs20

/-!
# Certificates of the listed shapes of `data111`, chunks 80..83
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_80 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_80 = true := by
  decide +kernel

theorem certs111_81 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_81 = true := by
  decide +kernel

theorem certs111_82 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_82 = true := by
  decide +kernel

theorem certs111_83 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_83 = true := by
  decide +kernel

end Collatz
