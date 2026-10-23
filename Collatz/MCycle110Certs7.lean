import Collatz.MCycle110Certs6

/-!
# Certificates of the listed shapes of `data110`, chunks 24..27
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_24 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_24 = true := by
  decide +kernel

theorem certs110_25 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_25 = true := by
  decide +kernel

theorem certs110_26 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_26 = true := by
  decide +kernel

theorem certs110_27 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_27 = true := by
  decide +kernel

end Collatz
