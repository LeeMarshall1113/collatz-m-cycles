import Collatz.MCycle111Certs43

/-!
# Certificates of the listed shapes of `data111`, chunks 172..175
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_172 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_172 = true := by
  decide +kernel

theorem certs111_173 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_173 = true := by
  decide +kernel

theorem certs111_174 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_174 = true := by
  decide +kernel

theorem certs111_175 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_175 = true := by
  decide +kernel

end Collatz
