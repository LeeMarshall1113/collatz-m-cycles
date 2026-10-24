import Collatz.MCycle111Certs180

/-!
# Certificates of the listed shapes of `data111`, chunks 720..723
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_720 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_720 = true := by
  decide +kernel

theorem certs111_721 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_721 = true := by
  decide +kernel

theorem certs111_722 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_722 = true := by
  decide +kernel

theorem certs111_723 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_723 = true := by
  decide +kernel

end Collatz
