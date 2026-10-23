import Collatz.MCycle110Certs81

/-!
# Certificates of the listed shapes of `data110`, chunks 324..327
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_324 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_324 = true := by
  decide +kernel

theorem certs110_325 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_325 = true := by
  decide +kernel

theorem certs110_326 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_326 = true := by
  decide +kernel

theorem certs110_327 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_327 = true := by
  decide +kernel

end Collatz
