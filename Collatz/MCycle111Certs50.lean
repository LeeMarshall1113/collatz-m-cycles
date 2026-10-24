import Collatz.MCycle111Certs49

/-!
# Certificates of the listed shapes of `data111`, chunks 196..199
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_196 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_196 = true := by
  decide +kernel

theorem certs111_197 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_197 = true := by
  decide +kernel

theorem certs111_198 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_198 = true := by
  decide +kernel

theorem certs111_199 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_199 = true := by
  decide +kernel

end Collatz
