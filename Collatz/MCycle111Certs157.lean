import Collatz.MCycle111Certs156

/-!
# Certificates of the listed shapes of `data111`, chunks 624..627
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_624 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_624 = true := by
  decide +kernel

theorem certs111_625 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_625 = true := by
  decide +kernel

theorem certs111_626 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_626 = true := by
  decide +kernel

theorem certs111_627 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_627 = true := by
  decide +kernel

end Collatz
