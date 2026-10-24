import Collatz.MCycle111Certs53

/-!
# Certificates of the listed shapes of `data111`, chunks 212..215
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_212 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_212 = true := by
  decide +kernel

theorem certs111_213 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_213 = true := by
  decide +kernel

theorem certs111_214 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_214 = true := by
  decide +kernel

theorem certs111_215 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_215 = true := by
  decide +kernel

end Collatz
