import Collatz.MCycle111Certs94

/-!
# Certificates of the listed shapes of `data111`, chunks 376..379
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_376 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_376 = true := by
  decide +kernel

theorem certs111_377 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_377 = true := by
  decide +kernel

theorem certs111_378 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_378 = true := by
  decide +kernel

theorem certs111_379 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_379 = true := by
  decide +kernel

end Collatz
