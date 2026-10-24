import Collatz.MCycle111Certs11

/-!
# Certificates of the listed shapes of `data111`, chunks 44..47
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_44 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_44 = true := by
  decide +kernel

theorem certs111_45 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_45 = true := by
  decide +kernel

theorem certs111_46 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_46 = true := by
  decide +kernel

theorem certs111_47 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_47 = true := by
  decide +kernel

end Collatz
