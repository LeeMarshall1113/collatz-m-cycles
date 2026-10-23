import Collatz.MCycle110Certs102

/-!
# Certificates of the listed shapes of `data110`, chunks 408..411
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_408 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_408 = true := by
  decide +kernel

theorem certs110_409 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_409 = true := by
  decide +kernel

theorem certs110_410 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_410 = true := by
  decide +kernel

theorem certs110_411 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_411 = true := by
  decide +kernel

end Collatz
