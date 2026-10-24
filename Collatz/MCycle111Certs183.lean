import Collatz.MCycle111Certs182

/-!
# Certificates of the listed shapes of `data111`, chunks 728..731
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_728 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_728 = true := by
  decide +kernel

theorem certs111_729 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_729 = true := by
  decide +kernel

theorem certs111_730 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_730 = true := by
  decide +kernel

theorem certs111_731 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_731 = true := by
  decide +kernel

end Collatz
