import Collatz.MCycle111Certs92

/-!
# Certificates of the listed shapes of `data111`, chunks 368..371
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_368 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_368 = true := by
  decide +kernel

theorem certs111_369 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_369 = true := by
  decide +kernel

theorem certs111_370 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_370 = true := by
  decide +kernel

theorem certs111_371 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_371 = true := by
  decide +kernel

end Collatz
