import Collatz.MCycle111Certs36

/-!
# Certificates of the listed shapes of `data111`, chunks 144..147
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_144 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_144 = true := by
  decide +kernel

theorem certs111_145 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_145 = true := by
  decide +kernel

theorem certs111_146 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_146 = true := by
  decide +kernel

theorem certs111_147 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_147 = true := by
  decide +kernel

end Collatz
