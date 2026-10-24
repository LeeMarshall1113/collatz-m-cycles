import Collatz.MCycle111Certs70

/-!
# Certificates of the listed shapes of `data111`, chunks 280..283
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_280 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_280 = true := by
  decide +kernel

theorem certs111_281 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_281 = true := by
  decide +kernel

theorem certs111_282 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_282 = true := by
  decide +kernel

theorem certs111_283 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_283 = true := by
  decide +kernel

end Collatz
