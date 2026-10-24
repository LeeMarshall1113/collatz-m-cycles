import Collatz.MCycle111Certs128

/-!
# Certificates of the listed shapes of `data111`, chunks 512..515
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_512 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_512 = true := by
  decide +kernel

theorem certs111_513 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_513 = true := by
  decide +kernel

theorem certs111_514 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_514 = true := by
  decide +kernel

theorem certs111_515 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_515 = true := by
  decide +kernel

end Collatz
