import Collatz.MCycle111Certs21

/-!
# Certificates of the listed shapes of `data111`, chunks 84..87
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_84 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_84 = true := by
  decide +kernel

theorem certs111_85 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_85 = true := by
  decide +kernel

theorem certs111_86 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_86 = true := by
  decide +kernel

theorem certs111_87 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_87 = true := by
  decide +kernel

end Collatz
