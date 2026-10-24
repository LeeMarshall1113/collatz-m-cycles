import Collatz.MCycle111Certs75

/-!
# Certificates of the listed shapes of `data111`, chunks 300..303
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_300 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_300 = true := by
  decide +kernel

theorem certs111_301 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_301 = true := by
  decide +kernel

theorem certs111_302 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_302 = true := by
  decide +kernel

theorem certs111_303 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_303 = true := by
  decide +kernel

end Collatz
