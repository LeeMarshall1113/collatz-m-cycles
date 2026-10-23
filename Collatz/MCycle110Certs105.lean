import Collatz.MCycle110Certs104

/-!
# Certificates of the listed shapes of `data110`, chunks 416..419
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_416 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_416 = true := by
  decide +kernel

theorem certs110_417 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_417 = true := by
  decide +kernel

theorem certs110_418 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_418 = true := by
  decide +kernel

theorem certs110_419 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_419 = true := by
  decide +kernel

end Collatz
