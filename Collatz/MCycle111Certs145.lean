import Collatz.MCycle111Certs144

/-!
# Certificates of the listed shapes of `data111`, chunks 576..579
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_576 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_576 = true := by
  decide +kernel

theorem certs111_577 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_577 = true := by
  decide +kernel

theorem certs111_578 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_578 = true := by
  decide +kernel

theorem certs111_579 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_579 = true := by
  decide +kernel

end Collatz
