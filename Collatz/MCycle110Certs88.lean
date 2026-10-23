import Collatz.MCycle110Certs87

/-!
# Certificates of the listed shapes of `data110`, chunks 348..351
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_348 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_348 = true := by
  decide +kernel

theorem certs110_349 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_349 = true := by
  decide +kernel

theorem certs110_350 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_350 = true := by
  decide +kernel

theorem certs110_351 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_351 = true := by
  decide +kernel

end Collatz
