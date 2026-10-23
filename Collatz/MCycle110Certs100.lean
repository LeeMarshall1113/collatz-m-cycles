import Collatz.MCycle110Certs99

/-!
# Certificates of the listed shapes of `data110`, chunks 396..399
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_396 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_396 = true := by
  decide +kernel

theorem certs110_397 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_397 = true := by
  decide +kernel

theorem certs110_398 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_398 = true := by
  decide +kernel

theorem certs110_399 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_399 = true := by
  decide +kernel

end Collatz
