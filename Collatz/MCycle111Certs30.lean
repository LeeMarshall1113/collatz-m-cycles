import Collatz.MCycle111Certs29

/-!
# Certificates of the listed shapes of `data111`, chunks 116..119
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_116 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_116 = true := by
  decide +kernel

theorem certs111_117 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_117 = true := by
  decide +kernel

theorem certs111_118 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_118 = true := by
  decide +kernel

theorem certs111_119 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_119 = true := by
  decide +kernel

end Collatz
