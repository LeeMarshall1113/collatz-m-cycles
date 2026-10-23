import Collatz.MCycle110Certs90

/-!
# Certificates of the listed shapes of `data110`, chunks 360..363
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_360 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_360 = true := by
  decide +kernel

theorem certs110_361 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_361 = true := by
  decide +kernel

theorem certs110_362 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_362 = true := by
  decide +kernel

theorem certs110_363 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_363 = true := by
  decide +kernel

end Collatz
