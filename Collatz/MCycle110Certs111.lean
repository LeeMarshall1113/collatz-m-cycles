import Collatz.MCycle110Certs110

/-!
# Certificates of the listed shapes of `data110`, chunks 440..443
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_440 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_440 = true := by
  decide +kernel

theorem certs110_441 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_441 = true := by
  decide +kernel

theorem certs110_442 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_442 = true := by
  decide +kernel

theorem certs110_443 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_443 = true := by
  decide +kernel

end Collatz
