import Collatz.MCycle111Certs37

/-!
# Certificates of the listed shapes of `data111`, chunks 148..151
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_148 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_148 = true := by
  decide +kernel

theorem certs111_149 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_149 = true := by
  decide +kernel

theorem certs111_150 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_150 = true := by
  decide +kernel

theorem certs111_151 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_151 = true := by
  decide +kernel

end Collatz
