import Collatz.MCycle111Certs56

/-!
# Certificates of the listed shapes of `data111`, chunks 224..227
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_224 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_224 = true := by
  decide +kernel

theorem certs111_225 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_225 = true := by
  decide +kernel

theorem certs111_226 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_226 = true := by
  decide +kernel

theorem certs111_227 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_227 = true := by
  decide +kernel

end Collatz
