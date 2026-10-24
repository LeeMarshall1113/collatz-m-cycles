import Collatz.MCycle111Certs129

/-!
# Certificates of the listed shapes of `data111`, chunks 516..519
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_516 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_516 = true := by
  decide +kernel

theorem certs111_517 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_517 = true := by
  decide +kernel

theorem certs111_518 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_518 = true := by
  decide +kernel

theorem certs111_519 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_519 = true := by
  decide +kernel

end Collatz
