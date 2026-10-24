import Collatz.MCycle111Certs157

/-!
# Certificates of the listed shapes of `data111`, chunks 628..631
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_628 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_628 = true := by
  decide +kernel

theorem certs111_629 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_629 = true := by
  decide +kernel

theorem certs111_630 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_630 = true := by
  decide +kernel

theorem certs111_631 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_631 = true := by
  decide +kernel

end Collatz
