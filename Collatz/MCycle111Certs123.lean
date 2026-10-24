import Collatz.MCycle111Certs122

/-!
# Certificates of the listed shapes of `data111`, chunks 488..491
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_488 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_488 = true := by
  decide +kernel

theorem certs111_489 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_489 = true := by
  decide +kernel

theorem certs111_490 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_490 = true := by
  decide +kernel

theorem certs111_491 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_491 = true := by
  decide +kernel

end Collatz
