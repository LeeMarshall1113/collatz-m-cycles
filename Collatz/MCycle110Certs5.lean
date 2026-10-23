import Collatz.MCycle110Certs4

/-!
# Certificates of the listed shapes of `data110`, chunks 16..19
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_16 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_16 = true := by
  decide +kernel

theorem certs110_17 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_17 = true := by
  decide +kernel

theorem certs110_18 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_18 = true := by
  decide +kernel

theorem certs110_19 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_19 = true := by
  decide +kernel

end Collatz
