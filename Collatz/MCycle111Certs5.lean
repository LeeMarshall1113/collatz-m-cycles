import Collatz.MCycle111Certs4

/-!
# Certificates of the listed shapes of `data111`, chunks 16..19
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_16 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_16 = true := by
  decide +kernel

theorem certs111_17 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_17 = true := by
  decide +kernel

theorem certs111_18 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_18 = true := by
  decide +kernel

theorem certs111_19 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_19 = true := by
  decide +kernel

end Collatz
