import Collatz.MCycle111Certs19

/-!
# Certificates of the listed shapes of `data111`, chunks 76..79
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_76 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_76 = true := by
  decide +kernel

theorem certs111_77 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_77 = true := by
  decide +kernel

theorem certs111_78 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_78 = true := by
  decide +kernel

theorem certs111_79 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_79 = true := by
  decide +kernel

end Collatz
