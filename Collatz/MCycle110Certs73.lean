import Collatz.MCycle110Certs72

/-!
# Certificates of the listed shapes of `data110`, chunks 288..291
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_288 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_288 = true := by
  decide +kernel

theorem certs110_289 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_289 = true := by
  decide +kernel

theorem certs110_290 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_290 = true := by
  decide +kernel

theorem certs110_291 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_291 = true := by
  decide +kernel

end Collatz
