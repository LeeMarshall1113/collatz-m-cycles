import Collatz.MCycle111Certs61

/-!
# Certificates of the listed shapes of `data111`, chunks 244..247
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_244 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_244 = true := by
  decide +kernel

theorem certs111_245 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_245 = true := by
  decide +kernel

theorem certs111_246 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_246 = true := by
  decide +kernel

theorem certs111_247 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_247 = true := by
  decide +kernel

end Collatz
