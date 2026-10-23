import Collatz.MCycle110Certs86

/-!
# Certificates of the listed shapes of `data110`, chunks 344..347
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_344 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_344 = true := by
  decide +kernel

theorem certs110_345 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_345 = true := by
  decide +kernel

theorem certs110_346 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_346 = true := by
  decide +kernel

theorem certs110_347 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_347 = true := by
  decide +kernel

end Collatz
