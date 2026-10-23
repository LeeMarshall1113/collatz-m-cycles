import Collatz.MCycle110Certs55

/-!
# Certificates of the listed shapes of `data110`, chunks 220..223
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_220 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_220 = true := by
  decide +kernel

theorem certs110_221 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_221 = true := by
  decide +kernel

theorem certs110_222 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_222 = true := by
  decide +kernel

theorem certs110_223 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_223 = true := by
  decide +kernel

end Collatz
