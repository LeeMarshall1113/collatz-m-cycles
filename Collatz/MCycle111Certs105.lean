import Collatz.MCycle111Certs104

/-!
# Certificates of the listed shapes of `data111`, chunks 416..419
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs111_416 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_416 = true := by
  decide +kernel

theorem certs111_417 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_417 = true := by
  decide +kernel

theorem certs111_418 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_418 = true := by
  decide +kernel

theorem certs111_419 : certsOK3D 111 20 grid111 grid3_111 data111.certs shapes111_419 = true := by
  decide +kernel

end Collatz
