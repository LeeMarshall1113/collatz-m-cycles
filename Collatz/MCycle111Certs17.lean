import Collatz.MCycle111Certs16

/-!
# Certificates of the listed shapes of `data111`, chunks 64..67
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_64 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_64 = true := by
  decide +kernel

theorem certs111_65 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_65 = true := by
  decide +kernel

theorem certs111_66 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_66 = true := by
  decide +kernel

theorem certs111_67 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_67 = true := by
  decide +kernel

end Collatz
