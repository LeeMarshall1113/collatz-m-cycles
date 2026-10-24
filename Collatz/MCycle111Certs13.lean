import Collatz.MCycle111Certs12

/-!
# Certificates of the listed shapes of `data111`, chunks 48..51
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_48 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_48 = true := by
  decide +kernel

theorem certs111_49 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_49 = true := by
  decide +kernel

theorem certs111_50 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_50 = true := by
  decide +kernel

theorem certs111_51 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_51 = true := by
  decide +kernel

end Collatz
