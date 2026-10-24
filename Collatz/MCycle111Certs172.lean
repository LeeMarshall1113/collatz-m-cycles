import Collatz.MCycle111Certs171

/-!
# Certificates of the listed shapes of `data111`, chunks 684..687
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_684 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_684 = true := by
  decide +kernel

theorem certs111_685 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_685 = true := by
  decide +kernel

theorem certs111_686 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_686 = true := by
  decide +kernel

theorem certs111_687 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_687 = true := by
  decide +kernel

end Collatz
