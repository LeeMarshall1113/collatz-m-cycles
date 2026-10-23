import Collatz.MCycle110Certs3

/-!
# Certificates of the listed shapes of `data110`, chunks 12..15
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_12 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_12 = true := by
  decide +kernel

theorem certs110_13 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_13 = true := by
  decide +kernel

theorem certs110_14 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_14 = true := by
  decide +kernel

theorem certs110_15 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_15 = true := by
  decide +kernel

end Collatz
