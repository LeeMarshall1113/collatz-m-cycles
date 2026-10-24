import Collatz.MCycle111Certs10

/-!
# Certificates of the listed shapes of `data111`, chunks 40..43
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_40 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_40 = true := by
  decide +kernel

theorem certs111_41 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_41 = true := by
  decide +kernel

theorem certs111_42 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_42 = true := by
  decide +kernel

theorem certs111_43 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_43 = true := by
  decide +kernel

end Collatz
