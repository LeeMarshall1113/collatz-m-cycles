import Collatz.MCycle111Certs38

/-!
# Certificates of the listed shapes of `data111`, chunks 152..155
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_152 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_152 = true := by
  decide +kernel

theorem certs111_153 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_153 = true := by
  decide +kernel

theorem certs111_154 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_154 = true := by
  decide +kernel

theorem certs111_155 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_155 = true := by
  decide +kernel

end Collatz
