import Collatz.MCycle111Certs22

/-!
# Certificates of the listed shapes of `data111`, chunks 88..91
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_88 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_88 = true := by
  decide +kernel

theorem certs111_89 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_89 = true := by
  decide +kernel

theorem certs111_90 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_90 = true := by
  decide +kernel

theorem certs111_91 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_91 = true := by
  decide +kernel

end Collatz
