import Collatz.MCycle111Certs26

/-!
# Certificates of the listed shapes of `data111`, chunks 104..107
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_104 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_104 = true := by
  decide +kernel

theorem certs111_105 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_105 = true := by
  decide +kernel

theorem certs111_106 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_106 = true := by
  decide +kernel

theorem certs111_107 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_107 = true := by
  decide +kernel

end Collatz
