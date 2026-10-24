import Collatz.MCycle111Certs184

/-!
# Certificates of the listed shapes of `data111`, chunks 736..739
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_736 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_736 = true := by
  decide +kernel

theorem certs111_737 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_737 = true := by
  decide +kernel

theorem certs111_738 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_738 = true := by
  decide +kernel

theorem certs111_739 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_739 = true := by
  decide +kernel

end Collatz
