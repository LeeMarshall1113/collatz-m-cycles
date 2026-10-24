import Collatz.MCycle111Certs63

/-!
# Certificates of the listed shapes of `data111`, chunks 252..255
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_252 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_252 = true := by
  decide +kernel

theorem certs111_253 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_253 = true := by
  decide +kernel

theorem certs111_254 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_254 = true := by
  decide +kernel

theorem certs111_255 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_255 = true := by
  decide +kernel

end Collatz
