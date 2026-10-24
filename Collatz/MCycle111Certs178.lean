import Collatz.MCycle111Certs177

/-!
# Certificates of the listed shapes of `data111`, chunks 708..711
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_708 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_708 = true := by
  decide +kernel

theorem certs111_709 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_709 = true := by
  decide +kernel

theorem certs111_710 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_710 = true := by
  decide +kernel

theorem certs111_711 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_711 = true := by
  decide +kernel

end Collatz
