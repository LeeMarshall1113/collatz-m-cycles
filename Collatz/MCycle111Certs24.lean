import Collatz.MCycle111Certs23

/-!
# Certificates of the listed shapes of `data111`, chunks 92..95
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_92 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_92 = true := by
  decide +kernel

theorem certs111_93 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_93 = true := by
  decide +kernel

theorem certs111_94 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_94 = true := by
  decide +kernel

theorem certs111_95 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_95 = true := by
  decide +kernel

end Collatz
