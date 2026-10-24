import Collatz.MCycle111Certs51

/-!
# Certificates of the listed shapes of `data111`, chunks 204..207
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_204 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_204 = true := by
  decide +kernel

theorem certs111_205 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_205 = true := by
  decide +kernel

theorem certs111_206 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_206 = true := by
  decide +kernel

theorem certs111_207 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_207 = true := by
  decide +kernel

end Collatz
