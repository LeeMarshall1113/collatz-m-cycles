import Collatz.MCycle110Certs76

/-!
# Certificates of the listed shapes of `data110`, chunks 304..307
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_304 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_304 = true := by
  decide +kernel

theorem certs110_305 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_305 = true := by
  decide +kernel

theorem certs110_306 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_306 = true := by
  decide +kernel

theorem certs110_307 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_307 = true := by
  decide +kernel

end Collatz
