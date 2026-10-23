import Collatz.MCycle110Certs100

/-!
# Certificates of the listed shapes of `data110`, chunks 400..403
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_400 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_400 = true := by
  decide +kernel

theorem certs110_401 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_401 = true := by
  decide +kernel

theorem certs110_402 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_402 = true := by
  decide +kernel

theorem certs110_403 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_403 = true := by
  decide +kernel

end Collatz
