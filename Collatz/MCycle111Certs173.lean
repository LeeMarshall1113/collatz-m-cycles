import Collatz.MCycle111Certs172

/-!
# Certificates of the listed shapes of `data111`, chunks 688..691
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_688 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_688 = true := by
  decide +kernel

theorem certs111_689 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_689 = true := by
  decide +kernel

theorem certs111_690 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_690 = true := by
  decide +kernel

theorem certs111_691 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_691 = true := by
  decide +kernel

end Collatz
