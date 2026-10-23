import Collatz.MCycle110Certs113

/-!
# Certificates of the listed shapes of `data110`, chunks 452..455
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_452 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_452 = true := by
  decide +kernel

theorem certs110_453 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_453 = true := by
  decide +kernel

theorem certs110_454 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_454 = true := by
  decide +kernel

theorem certs110_455 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_455 = true := by
  decide +kernel

end Collatz
