import Collatz.MCycle111Certs67

/-!
# Certificates of the listed shapes of `data111`, chunks 268..271
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_268 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_268 = true := by
  decide +kernel

theorem certs111_269 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_269 = true := by
  decide +kernel

theorem certs111_270 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_270 = true := by
  decide +kernel

theorem certs111_271 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_271 = true := by
  decide +kernel

end Collatz
