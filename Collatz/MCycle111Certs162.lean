import Collatz.MCycle111Certs161

/-!
# Certificates of the listed shapes of `data111`, chunks 644..647
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_644 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_644 = true := by
  decide +kernel

theorem certs111_645 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_645 = true := by
  decide +kernel

theorem certs111_646 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_646 = true := by
  decide +kernel

theorem certs111_647 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_647 = true := by
  decide +kernel

end Collatz
