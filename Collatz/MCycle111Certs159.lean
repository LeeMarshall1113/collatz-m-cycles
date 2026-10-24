import Collatz.MCycle111Certs158

/-!
# Certificates of the listed shapes of `data111`, chunks 632..635
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_632 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_632 = true := by
  decide +kernel

theorem certs111_633 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_633 = true := by
  decide +kernel

theorem certs111_634 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_634 = true := by
  decide +kernel

theorem certs111_635 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_635 = true := by
  decide +kernel

end Collatz
