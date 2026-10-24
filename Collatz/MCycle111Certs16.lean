import Collatz.MCycle111Certs15

/-!
# Certificates of the listed shapes of `data111`, chunks 60..63
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_60 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_60 = true := by
  decide +kernel

theorem certs111_61 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_61 = true := by
  decide +kernel

theorem certs111_62 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_62 = true := by
  decide +kernel

theorem certs111_63 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_63 = true := by
  decide +kernel

end Collatz
