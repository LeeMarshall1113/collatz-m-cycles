import Collatz.MCycle110Certs107

/-!
# Certificates of the listed shapes of `data110`, chunks 428..431
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_428 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_428 = true := by
  decide +kernel

theorem certs110_429 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_429 = true := by
  decide +kernel

theorem certs110_430 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_430 = true := by
  decide +kernel

theorem certs110_431 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_431 = true := by
  decide +kernel

end Collatz
