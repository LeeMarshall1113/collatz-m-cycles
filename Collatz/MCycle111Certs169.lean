import Collatz.MCycle111Certs168

/-!
# Certificates of the listed shapes of `data111`, chunks 672..675
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_672 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_672 = true := by
  decide +kernel

theorem certs111_673 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_673 = true := by
  decide +kernel

theorem certs111_674 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_674 = true := by
  decide +kernel

theorem certs111_675 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_675 = true := by
  decide +kernel

end Collatz
