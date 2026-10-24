import Collatz.MCycle111Certs159

/-!
# Certificates of the listed shapes of `data111`, chunks 636..639
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_636 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_636 = true := by
  decide +kernel

theorem certs111_637 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_637 = true := by
  decide +kernel

theorem certs111_638 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_638 = true := by
  decide +kernel

theorem certs111_639 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_639 = true := by
  decide +kernel

end Collatz
