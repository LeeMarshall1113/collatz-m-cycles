import Collatz.MCycle111Certs62

/-!
# Certificates of the listed shapes of `data111`, chunks 248..251
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_248 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_248 = true := by
  decide +kernel

theorem certs111_249 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_249 = true := by
  decide +kernel

theorem certs111_250 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_250 = true := by
  decide +kernel

theorem certs111_251 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_251 = true := by
  decide +kernel

end Collatz
