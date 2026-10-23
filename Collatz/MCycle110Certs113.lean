import Collatz.MCycle110Certs112

/-!
# Certificates of the listed shapes of `data110`, chunks 448..451
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_448 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_448 = true := by
  decide +kernel

theorem certs110_449 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_449 = true := by
  decide +kernel

theorem certs110_450 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_450 = true := by
  decide +kernel

theorem certs110_451 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_451 = true := by
  decide +kernel

end Collatz
