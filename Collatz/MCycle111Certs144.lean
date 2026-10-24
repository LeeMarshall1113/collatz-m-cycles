import Collatz.MCycle111Certs143

/-!
# Certificates of the listed shapes of `data111`, chunks 572..575
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_572 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_572 = true := by
  decide +kernel

theorem certs111_573 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_573 = true := by
  decide +kernel

theorem certs111_574 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_574 = true := by
  decide +kernel

theorem certs111_575 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_575 = true := by
  decide +kernel

end Collatz
