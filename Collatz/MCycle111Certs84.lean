import Collatz.MCycle111Certs83

/-!
# Certificates of the listed shapes of `data111`, chunks 332..335
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_332 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_332 = true := by
  decide +kernel

theorem certs111_333 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_333 = true := by
  decide +kernel

theorem certs111_334 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_334 = true := by
  decide +kernel

theorem certs111_335 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_335 = true := by
  decide +kernel

end Collatz
