import Collatz.MCycle111Certs162

/-!
# Certificates of the listed shapes of `data111`, chunks 648..651
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_648 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_648 = true := by
  decide +kernel

theorem certs111_649 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_649 = true := by
  decide +kernel

theorem certs111_650 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_650 = true := by
  decide +kernel

theorem certs111_651 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_651 = true := by
  decide +kernel

end Collatz
