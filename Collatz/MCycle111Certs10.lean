import Collatz.MCycle111Certs9

/-!
# Certificates of the listed shapes of `data111`, chunks 36..39
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_36 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_36 = true := by
  decide +kernel

theorem certs111_37 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_37 = true := by
  decide +kernel

theorem certs111_38 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_38 = true := by
  decide +kernel

theorem certs111_39 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_39 = true := by
  decide +kernel

end Collatz
