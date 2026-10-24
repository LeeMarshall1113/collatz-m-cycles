import Collatz.MCycle111Certs41

/-!
# Certificates of the listed shapes of `data111`, chunks 164..167
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_164 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_164 = true := by
  decide +kernel

theorem certs111_165 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_165 = true := by
  decide +kernel

theorem certs111_166 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_166 = true := by
  decide +kernel

theorem certs111_167 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_167 = true := by
  decide +kernel

end Collatz
