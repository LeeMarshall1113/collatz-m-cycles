import Collatz.MCycle110Certs85

/-!
# Certificates of the listed shapes of `data110`, chunks 340..343
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_340 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_340 = true := by
  decide +kernel

theorem certs110_341 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_341 = true := by
  decide +kernel

theorem certs110_342 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_342 = true := by
  decide +kernel

theorem certs110_343 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_343 = true := by
  decide +kernel

end Collatz
