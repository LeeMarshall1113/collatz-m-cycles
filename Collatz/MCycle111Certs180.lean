import Collatz.MCycle111Certs179

/-!
# Certificates of the listed shapes of `data111`, chunks 716..719
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_716 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_716 = true := by
  decide +kernel

theorem certs111_717 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_717 = true := by
  decide +kernel

theorem certs111_718 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_718 = true := by
  decide +kernel

theorem certs111_719 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_719 = true := by
  decide +kernel

end Collatz
