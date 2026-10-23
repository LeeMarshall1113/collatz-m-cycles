import Collatz.MCycle110Certs73

/-!
# Certificates of the listed shapes of `data110`, chunks 292..295
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_292 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_292 = true := by
  decide +kernel

theorem certs110_293 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_293 = true := by
  decide +kernel

theorem certs110_294 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_294 = true := by
  decide +kernel

theorem certs110_295 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_295 = true := by
  decide +kernel

end Collatz
