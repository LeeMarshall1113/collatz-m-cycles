import Collatz.MCycle110Certs84

/-!
# Certificates of the listed shapes of `data110`, chunks 336..339
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_336 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_336 = true := by
  decide +kernel

theorem certs110_337 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_337 = true := by
  decide +kernel

theorem certs110_338 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_338 = true := by
  decide +kernel

theorem certs110_339 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_339 = true := by
  decide +kernel

end Collatz
