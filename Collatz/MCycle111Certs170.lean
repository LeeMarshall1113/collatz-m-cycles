import Collatz.MCycle111Certs169

/-!
# Certificates of the listed shapes of `data111`, chunks 676..679
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_676 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_676 = true := by
  decide +kernel

theorem certs111_677 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_677 = true := by
  decide +kernel

theorem certs111_678 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_678 = true := by
  decide +kernel

theorem certs111_679 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_679 = true := by
  decide +kernel

end Collatz
