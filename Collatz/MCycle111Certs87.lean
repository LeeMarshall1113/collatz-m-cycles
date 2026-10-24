import Collatz.MCycle111Certs86

/-!
# Certificates of the listed shapes of `data111`, chunks 344..347
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_344 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_344 = true := by
  decide +kernel

theorem certs111_345 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_345 = true := by
  decide +kernel

theorem certs111_346 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_346 = true := by
  decide +kernel

theorem certs111_347 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_347 = true := by
  decide +kernel

end Collatz
