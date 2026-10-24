import Collatz.MCycle111Certs132

/-!
# Certificates of the listed shapes of `data111`, chunks 528..531
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_528 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_528 = true := by
  decide +kernel

theorem certs111_529 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_529 = true := by
  decide +kernel

theorem certs111_530 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_530 = true := by
  decide +kernel

theorem certs111_531 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_531 = true := by
  decide +kernel

end Collatz
