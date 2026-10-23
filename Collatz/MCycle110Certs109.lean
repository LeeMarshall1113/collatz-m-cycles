import Collatz.MCycle110Certs108

/-!
# Certificates of the listed shapes of `data110`, chunks 432..435
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_432 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_432 = true := by
  decide +kernel

theorem certs110_433 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_433 = true := by
  decide +kernel

theorem certs110_434 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_434 = true := by
  decide +kernel

theorem certs110_435 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_435 = true := by
  decide +kernel

end Collatz
