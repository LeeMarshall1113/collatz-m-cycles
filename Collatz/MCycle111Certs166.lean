import Collatz.MCycle111Certs165

/-!
# Certificates of the listed shapes of `data111`, chunks 660..663
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_660 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_660 = true := by
  decide +kernel

theorem certs111_661 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_661 = true := by
  decide +kernel

theorem certs111_662 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_662 = true := by
  decide +kernel

theorem certs111_663 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_663 = true := by
  decide +kernel

end Collatz
