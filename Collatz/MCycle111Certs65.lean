import Collatz.MCycle111Certs64

/-!
# Certificates of the listed shapes of `data111`, chunks 256..259
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_256 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_256 = true := by
  decide +kernel

theorem certs111_257 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_257 = true := by
  decide +kernel

theorem certs111_258 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_258 = true := by
  decide +kernel

theorem certs111_259 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_259 = true := by
  decide +kernel

end Collatz
