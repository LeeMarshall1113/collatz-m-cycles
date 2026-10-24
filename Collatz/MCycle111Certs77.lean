import Collatz.MCycle111Certs76

/-!
# Certificates of the listed shapes of `data111`, chunks 304..307
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_304 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_304 = true := by
  decide +kernel

theorem certs111_305 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_305 = true := by
  decide +kernel

theorem certs111_306 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_306 = true := by
  decide +kernel

theorem certs111_307 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_307 = true := by
  decide +kernel

end Collatz
