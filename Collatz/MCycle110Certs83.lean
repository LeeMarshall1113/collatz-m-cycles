import Collatz.MCycle110Certs82

/-!
# Certificates of the listed shapes of `data110`, chunks 328..331
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_328 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_328 = true := by
  decide +kernel

theorem certs110_329 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_329 = true := by
  decide +kernel

theorem certs110_330 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_330 = true := by
  decide +kernel

theorem certs110_331 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_331 = true := by
  decide +kernel

end Collatz
