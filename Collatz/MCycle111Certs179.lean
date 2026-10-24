import Collatz.MCycle111Certs178

/-!
# Certificates of the listed shapes of `data111`, chunks 712..715
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_712 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_712 = true := by
  decide +kernel

theorem certs111_713 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_713 = true := by
  decide +kernel

theorem certs111_714 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_714 = true := by
  decide +kernel

theorem certs111_715 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_715 = true := by
  decide +kernel

end Collatz
