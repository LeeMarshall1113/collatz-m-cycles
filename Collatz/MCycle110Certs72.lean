import Collatz.MCycle110Certs71

/-!
# Certificates of the listed shapes of `data110`, chunks 284..287
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_284 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_284 = true := by
  decide +kernel

theorem certs110_285 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_285 = true := by
  decide +kernel

theorem certs110_286 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_286 = true := by
  decide +kernel

theorem certs110_287 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_287 = true := by
  decide +kernel

end Collatz
