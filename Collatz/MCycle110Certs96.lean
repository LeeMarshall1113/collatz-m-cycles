import Collatz.MCycle110Certs95

/-!
# Certificates of the listed shapes of `data110`, chunks 380..383
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_380 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_380 = true := by
  decide +kernel

theorem certs110_381 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_381 = true := by
  decide +kernel

theorem certs110_382 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_382 = true := by
  decide +kernel

theorem certs110_383 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_383 = true := by
  decide +kernel

end Collatz
