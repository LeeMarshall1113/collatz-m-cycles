import Collatz.MCycle111Certs109

/-!
# Certificates of the listed shapes of `data111`, chunks 436..439
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_436 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_436 = true := by
  decide +kernel

theorem certs111_437 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_437 = true := by
  decide +kernel

theorem certs111_438 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_438 = true := by
  decide +kernel

theorem certs111_439 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_439 = true := by
  decide +kernel

end Collatz
