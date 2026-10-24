import Collatz.MCycle111Certs185

/-!
# Certificates of the listed shapes of `data111`, chunks 740..740
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_740 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_740 = true := by
  decide +kernel

end Collatz
