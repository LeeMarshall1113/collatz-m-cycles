import Collatz.MCycle111Certs183

/-!
# Certificates of the listed shapes of `data111`, chunks 732..735
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_732 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_732 = true := by
  decide +kernel

theorem certs111_733 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_733 = true := by
  decide +kernel

theorem certs111_734 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_734 = true := by
  decide +kernel

theorem certs111_735 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_735 = true := by
  decide +kernel

end Collatz
