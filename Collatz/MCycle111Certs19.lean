import Collatz.MCycle111Certs18

/-!
# Certificates of the listed shapes of `data111`, chunks 72..75
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_72 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_72 = true := by
  decide +kernel

theorem certs111_73 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_73 = true := by
  decide +kernel

theorem certs111_74 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_74 = true := by
  decide +kernel

theorem certs111_75 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_75 = true := by
  decide +kernel

end Collatz
