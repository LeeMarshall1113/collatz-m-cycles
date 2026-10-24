import Collatz.MCycle111Certs176

/-!
# Certificates of the listed shapes of `data111`, chunks 704..707
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_704 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_704 = true := by
  decide +kernel

theorem certs111_705 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_705 = true := by
  decide +kernel

theorem certs111_706 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_706 = true := by
  decide +kernel

theorem certs111_707 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_707 = true := by
  decide +kernel

end Collatz
