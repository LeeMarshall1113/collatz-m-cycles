import Collatz.MCycle111Certs27

/-!
# Certificates of the listed shapes of `data111`, chunks 108..111
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_108 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_108 = true := by
  decide +kernel

theorem certs111_109 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_109 = true := by
  decide +kernel

theorem certs111_110 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_110 = true := by
  decide +kernel

theorem certs111_111 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_111 = true := by
  decide +kernel

end Collatz
