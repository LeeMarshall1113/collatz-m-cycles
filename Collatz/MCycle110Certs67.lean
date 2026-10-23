import Collatz.MCycle110Certs66

/-!
# Certificates of the listed shapes of `data110`, chunks 264..267
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_264 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_264 = true := by
  decide +kernel

theorem certs110_265 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_265 = true := by
  decide +kernel

theorem certs110_266 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_266 = true := by
  decide +kernel

theorem certs110_267 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_267 = true := by
  decide +kernel

end Collatz
