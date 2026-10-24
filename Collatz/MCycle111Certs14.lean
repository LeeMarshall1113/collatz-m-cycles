import Collatz.MCycle111Certs13

/-!
# Certificates of the listed shapes of `data111`, chunks 52..55
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_52 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_52 = true := by
  decide +kernel

theorem certs111_53 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_53 = true := by
  decide +kernel

theorem certs111_54 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_54 = true := by
  decide +kernel

theorem certs111_55 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_55 = true := by
  decide +kernel

end Collatz
