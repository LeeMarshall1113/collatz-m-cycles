import Collatz.MCycle111Certs111

/-!
# Certificates of the listed shapes of `data111`, chunks 444..447
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_444 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_444 = true := by
  decide +kernel

theorem certs111_445 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_445 = true := by
  decide +kernel

theorem certs111_446 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_446 = true := by
  decide +kernel

theorem certs111_447 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_447 = true := by
  decide +kernel

end Collatz
