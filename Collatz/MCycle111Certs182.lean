import Collatz.MCycle111Certs181

/-!
# Certificates of the listed shapes of `data111`, chunks 724..727
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_724 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_724 = true := by
  decide +kernel

theorem certs111_725 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_725 = true := by
  decide +kernel

theorem certs111_726 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_726 = true := by
  decide +kernel

theorem certs111_727 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_727 = true := by
  decide +kernel

end Collatz
