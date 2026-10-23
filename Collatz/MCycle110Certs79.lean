import Collatz.MCycle110Certs78

/-!
# Certificates of the listed shapes of `data110`, chunks 312..315
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_312 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_312 = true := by
  decide +kernel

theorem certs110_313 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_313 = true := by
  decide +kernel

theorem certs110_314 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_314 = true := by
  decide +kernel

theorem certs110_315 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_315 = true := by
  decide +kernel

end Collatz
