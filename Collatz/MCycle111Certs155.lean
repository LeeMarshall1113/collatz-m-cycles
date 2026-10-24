import Collatz.MCycle111Certs154

/-!
# Certificates of the listed shapes of `data111`, chunks 616..619
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_616 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_616 = true := by
  decide +kernel

theorem certs111_617 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_617 = true := by
  decide +kernel

theorem certs111_618 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_618 = true := by
  decide +kernel

theorem certs111_619 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_619 = true := by
  decide +kernel

end Collatz
