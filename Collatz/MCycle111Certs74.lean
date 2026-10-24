import Collatz.MCycle111Certs73

/-!
# Certificates of the listed shapes of `data111`, chunks 292..295
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_292 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_292 = true := by
  decide +kernel

theorem certs111_293 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_293 = true := by
  decide +kernel

theorem certs111_294 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_294 = true := by
  decide +kernel

theorem certs111_295 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_295 = true := by
  decide +kernel

end Collatz
