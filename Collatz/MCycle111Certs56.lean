import Collatz.MCycle111Certs55

/-!
# Certificates of the listed shapes of `data111`, chunks 220..223
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_220 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_220 = true := by
  decide +kernel

theorem certs111_221 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_221 = true := by
  decide +kernel

theorem certs111_222 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_222 = true := by
  decide +kernel

theorem certs111_223 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_223 = true := by
  decide +kernel

end Collatz
