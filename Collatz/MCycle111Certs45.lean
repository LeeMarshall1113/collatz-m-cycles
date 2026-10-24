import Collatz.MCycle111Certs44

/-!
# Certificates of the listed shapes of `data111`, chunks 176..179
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_176 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_176 = true := by
  decide +kernel

theorem certs111_177 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_177 = true := by
  decide +kernel

theorem certs111_178 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_178 = true := by
  decide +kernel

theorem certs111_179 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_179 = true := by
  decide +kernel

end Collatz
