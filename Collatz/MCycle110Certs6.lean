import Collatz.MCycle110Certs5

/-!
# Certificates of the listed shapes of `data110`, chunks 20..23
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_20 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_20 = true := by
  decide +kernel

theorem certs110_21 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_21 = true := by
  decide +kernel

theorem certs110_22 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_22 = true := by
  decide +kernel

theorem certs110_23 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_23 = true := by
  decide +kernel

end Collatz
