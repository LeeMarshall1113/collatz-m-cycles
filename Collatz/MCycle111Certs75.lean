import Collatz.MCycle111Certs74

/-!
# Certificates of the listed shapes of `data111`, chunks 296..299
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_296 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_296 = true := by
  decide +kernel

theorem certs111_297 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_297 = true := by
  decide +kernel

theorem certs111_298 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_298 = true := by
  decide +kernel

theorem certs111_299 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_299 = true := by
  decide +kernel

end Collatz
