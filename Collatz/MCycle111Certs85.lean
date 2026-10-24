import Collatz.MCycle111Certs84

/-!
# Certificates of the listed shapes of `data111`, chunks 336..339
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_336 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_336 = true := by
  decide +kernel

theorem certs111_337 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_337 = true := by
  decide +kernel

theorem certs111_338 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_338 = true := by
  decide +kernel

theorem certs111_339 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_339 = true := by
  decide +kernel

end Collatz
