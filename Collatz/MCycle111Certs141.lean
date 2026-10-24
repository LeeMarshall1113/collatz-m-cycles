import Collatz.MCycle111Certs140

/-!
# Certificates of the listed shapes of `data111`, chunks 560..563
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_560 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_560 = true := by
  decide +kernel

theorem certs111_561 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_561 = true := by
  decide +kernel

theorem certs111_562 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_562 = true := by
  decide +kernel

theorem certs111_563 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_563 = true := by
  decide +kernel

end Collatz
