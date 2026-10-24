import Collatz.MCycle111Certs17

/-!
# Certificates of the listed shapes of `data111`, chunks 68..71
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_68 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_68 = true := by
  decide +kernel

theorem certs111_69 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_69 = true := by
  decide +kernel

theorem certs111_70 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_70 = true := by
  decide +kernel

theorem certs111_71 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_71 = true := by
  decide +kernel

end Collatz
