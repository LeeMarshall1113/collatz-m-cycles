import Collatz.MCycle110Certs91

/-!
# Certificates of the listed shapes of `data110`, chunks 364..367
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_364 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_364 = true := by
  decide +kernel

theorem certs110_365 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_365 = true := by
  decide +kernel

theorem certs110_366 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_366 = true := by
  decide +kernel

theorem certs110_367 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_367 = true := by
  decide +kernel

end Collatz
