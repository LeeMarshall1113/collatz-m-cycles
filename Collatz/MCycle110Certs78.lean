import Collatz.MCycle110Certs77

/-!
# Certificates of the listed shapes of `data110`, chunks 308..311
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_308 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_308 = true := by
  decide +kernel

theorem certs110_309 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_309 = true := by
  decide +kernel

theorem certs110_310 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_310 = true := by
  decide +kernel

theorem certs110_311 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_311 = true := by
  decide +kernel

end Collatz
