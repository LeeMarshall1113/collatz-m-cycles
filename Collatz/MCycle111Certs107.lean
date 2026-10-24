import Collatz.MCycle111Certs106

/-!
# Certificates of the listed shapes of `data111`, chunks 424..427
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_424 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_424 = true := by
  decide +kernel

theorem certs111_425 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_425 = true := by
  decide +kernel

theorem certs111_426 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_426 = true := by
  decide +kernel

theorem certs111_427 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_427 = true := by
  decide +kernel

end Collatz
