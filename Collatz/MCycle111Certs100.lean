import Collatz.MCycle111Certs99

/-!
# Certificates of the listed shapes of `data111`, chunks 396..399
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_396 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_396 = true := by
  decide +kernel

theorem certs111_397 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_397 = true := by
  decide +kernel

theorem certs111_398 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_398 = true := by
  decide +kernel

theorem certs111_399 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_399 = true := by
  decide +kernel

end Collatz
