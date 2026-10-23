import Collatz.MCycle110Certs92

/-!
# Certificates of the listed shapes of `data110`, chunks 368..371
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_368 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_368 = true := by
  decide +kernel

theorem certs110_369 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_369 = true := by
  decide +kernel

theorem certs110_370 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_370 = true := by
  decide +kernel

theorem certs110_371 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_371 = true := by
  decide +kernel

end Collatz
