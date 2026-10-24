import Collatz.MCycle111Certs57

/-!
# Certificates of the listed shapes of `data111`, chunks 228..231
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_228 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_228 = true := by
  decide +kernel

theorem certs111_229 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_229 = true := by
  decide +kernel

theorem certs111_230 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_230 = true := by
  decide +kernel

theorem certs111_231 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_231 = true := by
  decide +kernel

end Collatz
