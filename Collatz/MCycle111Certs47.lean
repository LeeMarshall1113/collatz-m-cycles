import Collatz.MCycle111Certs46

/-!
# Certificates of the listed shapes of `data111`, chunks 184..187
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_184 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_184 = true := by
  decide +kernel

theorem certs111_185 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_185 = true := by
  decide +kernel

theorem certs111_186 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_186 = true := by
  decide +kernel

theorem certs111_187 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_187 = true := by
  decide +kernel

end Collatz
