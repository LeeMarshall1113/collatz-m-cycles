import Collatz.MCycle111Certs88

/-!
# Certificates of the listed shapes of `data111`, chunks 352..355
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_352 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_352 = true := by
  decide +kernel

theorem certs111_353 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_353 = true := by
  decide +kernel

theorem certs111_354 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_354 = true := by
  decide +kernel

theorem certs111_355 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_355 = true := by
  decide +kernel

end Collatz
