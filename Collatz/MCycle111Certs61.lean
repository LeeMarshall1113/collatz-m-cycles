import Collatz.MCycle111Certs60

/-!
# Certificates of the listed shapes of `data111`, chunks 240..243
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_240 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_240 = true := by
  decide +kernel

theorem certs111_241 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_241 = true := by
  decide +kernel

theorem certs111_242 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_242 = true := by
  decide +kernel

theorem certs111_243 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_243 = true := by
  decide +kernel

end Collatz
