import Collatz.MCycle111Certs40

/-!
# Certificates of the listed shapes of `data111`, chunks 160..163
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_160 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_160 = true := by
  decide +kernel

theorem certs111_161 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_161 = true := by
  decide +kernel

theorem certs111_162 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_162 = true := by
  decide +kernel

theorem certs111_163 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_163 = true := by
  decide +kernel

end Collatz
