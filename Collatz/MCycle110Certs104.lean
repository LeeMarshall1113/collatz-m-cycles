import Collatz.MCycle110Certs103

/-!
# Certificates of the listed shapes of `data110`, chunks 412..415
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_412 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_412 = true := by
  decide +kernel

theorem certs110_413 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_413 = true := by
  decide +kernel

theorem certs110_414 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_414 = true := by
  decide +kernel

theorem certs110_415 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_415 = true := by
  decide +kernel

end Collatz
