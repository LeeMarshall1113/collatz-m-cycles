import Collatz.MCycle110Certs58

/-!
# Certificates of the listed shapes of `data110`, chunks 232..235
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_232 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_232 = true := by
  decide +kernel

theorem certs110_233 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_233 = true := by
  decide +kernel

theorem certs110_234 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_234 = true := by
  decide +kernel

theorem certs110_235 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_235 = true := by
  decide +kernel

end Collatz
