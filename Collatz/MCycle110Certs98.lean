import Collatz.MCycle110Certs97

/-!
# Certificates of the listed shapes of `data110`, chunks 388..391
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_388 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_388 = true := by
  decide +kernel

theorem certs110_389 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_389 = true := by
  decide +kernel

theorem certs110_390 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_390 = true := by
  decide +kernel

theorem certs110_391 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_391 = true := by
  decide +kernel

end Collatz
