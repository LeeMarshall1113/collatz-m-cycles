import Collatz.MCycle111Certs24

/-!
# Certificates of the listed shapes of `data111`, chunks 96..99
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_96 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_96 = true := by
  decide +kernel

theorem certs111_97 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_97 = true := by
  decide +kernel

theorem certs111_98 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_98 = true := by
  decide +kernel

theorem certs111_99 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_99 = true := by
  decide +kernel

end Collatz
