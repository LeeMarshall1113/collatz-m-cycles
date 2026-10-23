import Collatz.MCycle110Certs69

/-!
# Certificates of the listed shapes of `data110`, chunks 276..279
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_276 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_276 = true := by
  decide +kernel

theorem certs110_277 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_277 = true := by
  decide +kernel

theorem certs110_278 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_278 = true := by
  decide +kernel

theorem certs110_279 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_279 = true := by
  decide +kernel

end Collatz
