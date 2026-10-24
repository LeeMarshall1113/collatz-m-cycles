import Collatz.MCycle111Certs98

/-!
# Certificates of the listed shapes of `data111`, chunks 392..395
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_392 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_392 = true := by
  decide +kernel

theorem certs111_393 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_393 = true := by
  decide +kernel

theorem certs111_394 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_394 = true := by
  decide +kernel

theorem certs111_395 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_395 = true := by
  decide +kernel

end Collatz
