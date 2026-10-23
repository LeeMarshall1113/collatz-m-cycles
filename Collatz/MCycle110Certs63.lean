import Collatz.MCycle110Certs62

/-!
# Certificates of the listed shapes of `data110`, chunks 248..251
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_248 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_248 = true := by
  decide +kernel

theorem certs110_249 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_249 = true := by
  decide +kernel

theorem certs110_250 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_250 = true := by
  decide +kernel

theorem certs110_251 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_251 = true := by
  decide +kernel

end Collatz
