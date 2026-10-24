import Collatz.MCycle111Certs34

/-!
# Certificates of the listed shapes of `data111`, chunks 136..139
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_136 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_136 = true := by
  decide +kernel

theorem certs111_137 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_137 = true := by
  decide +kernel

theorem certs111_138 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_138 = true := by
  decide +kernel

theorem certs111_139 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_139 = true := by
  decide +kernel

end Collatz
