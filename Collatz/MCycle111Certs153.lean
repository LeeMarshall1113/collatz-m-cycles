import Collatz.MCycle111Certs152

/-!
# Certificates of the listed shapes of `data111`, chunks 608..611
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_608 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_608 = true := by
  decide +kernel

theorem certs111_609 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_609 = true := by
  decide +kernel

theorem certs111_610 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_610 = true := by
  decide +kernel

theorem certs111_611 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_611 = true := by
  decide +kernel

end Collatz
