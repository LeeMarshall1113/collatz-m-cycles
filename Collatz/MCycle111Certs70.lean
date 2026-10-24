import Collatz.MCycle111Certs69

/-!
# Certificates of the listed shapes of `data111`, chunks 276..279
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_276 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_276 = true := by
  decide +kernel

theorem certs111_277 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_277 = true := by
  decide +kernel

theorem certs111_278 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_278 = true := by
  decide +kernel

theorem certs111_279 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_279 = true := by
  decide +kernel

end Collatz
