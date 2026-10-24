import Collatz.MCycle111Certs30

/-!
# Certificates of the listed shapes of `data111`, chunks 120..123
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_120 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_120 = true := by
  decide +kernel

theorem certs111_121 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_121 = true := by
  decide +kernel

theorem certs111_122 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_122 = true := by
  decide +kernel

theorem certs111_123 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_123 = true := by
  decide +kernel

end Collatz
