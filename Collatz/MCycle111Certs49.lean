import Collatz.MCycle111Certs48

/-!
# Certificates of the listed shapes of `data111`, chunks 192..195
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_192 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_192 = true := by
  decide +kernel

theorem certs111_193 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_193 = true := by
  decide +kernel

theorem certs111_194 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_194 = true := by
  decide +kernel

theorem certs111_195 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_195 = true := by
  decide +kernel

end Collatz
