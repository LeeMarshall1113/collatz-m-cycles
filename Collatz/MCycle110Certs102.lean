import Collatz.MCycle110Certs101

/-!
# Certificates of the listed shapes of `data110`, chunks 404..407
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_404 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_404 = true := by
  decide +kernel

theorem certs110_405 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_405 = true := by
  decide +kernel

theorem certs110_406 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_406 = true := by
  decide +kernel

theorem certs110_407 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_407 = true := by
  decide +kernel

end Collatz
