import Collatz.MCycle111Certs45

/-!
# Certificates of the listed shapes of `data111`, chunks 180..183
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_180 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_180 = true := by
  decide +kernel

theorem certs111_181 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_181 = true := by
  decide +kernel

theorem certs111_182 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_182 = true := by
  decide +kernel

theorem certs111_183 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_183 = true := by
  decide +kernel

end Collatz
