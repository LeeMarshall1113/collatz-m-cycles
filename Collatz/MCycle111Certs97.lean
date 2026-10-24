import Collatz.MCycle111Certs96

/-!
# Certificates of the listed shapes of `data111`, chunks 384..387
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_384 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_384 = true := by
  decide +kernel

theorem certs111_385 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_385 = true := by
  decide +kernel

theorem certs111_386 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_386 = true := by
  decide +kernel

theorem certs111_387 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_387 = true := by
  decide +kernel

end Collatz
