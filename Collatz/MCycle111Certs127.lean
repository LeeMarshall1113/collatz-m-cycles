import Collatz.MCycle111Certs126

/-!
# Certificates of the listed shapes of `data111`, chunks 504..507
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_504 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_504 = true := by
  decide +kernel

theorem certs111_505 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_505 = true := by
  decide +kernel

theorem certs111_506 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_506 = true := by
  decide +kernel

theorem certs111_507 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_507 = true := by
  decide +kernel

end Collatz
