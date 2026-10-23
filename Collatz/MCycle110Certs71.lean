import Collatz.MCycle110Certs70

/-!
# Certificates of the listed shapes of `data110`, chunks 280..283
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_280 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_280 = true := by
  decide +kernel

theorem certs110_281 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_281 = true := by
  decide +kernel

theorem certs110_282 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_282 = true := by
  decide +kernel

theorem certs110_283 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_283 = true := by
  decide +kernel

end Collatz
