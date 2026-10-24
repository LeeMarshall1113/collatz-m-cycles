import Collatz.MCycle111Certs42

/-!
# Certificates of the listed shapes of `data111`, chunks 168..171
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_168 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_168 = true := by
  decide +kernel

theorem certs111_169 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_169 = true := by
  decide +kernel

theorem certs111_170 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_170 = true := by
  decide +kernel

theorem certs111_171 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_171 = true := by
  decide +kernel

end Collatz
