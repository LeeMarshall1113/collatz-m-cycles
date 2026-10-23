import Collatz.MCycle110Certs93

/-!
# Certificates of the listed shapes of `data110`, chunks 372..375
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_372 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_372 = true := by
  decide +kernel

theorem certs110_373 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_373 = true := by
  decide +kernel

theorem certs110_374 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_374 = true := by
  decide +kernel

theorem certs110_375 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_375 = true := by
  decide +kernel

end Collatz
