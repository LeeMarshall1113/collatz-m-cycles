import Collatz.MCycle110Certs61

/-!
# Certificates of the listed shapes of `data110`, chunks 244..247
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_244 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_244 = true := by
  decide +kernel

theorem certs110_245 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_245 = true := by
  decide +kernel

theorem certs110_246 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_246 = true := by
  decide +kernel

theorem certs110_247 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_247 = true := by
  decide +kernel

end Collatz
