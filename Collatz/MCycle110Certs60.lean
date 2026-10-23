import Collatz.MCycle110Certs59

/-!
# Certificates of the listed shapes of `data110`, chunks 236..239
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_236 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_236 = true := by
  decide +kernel

theorem certs110_237 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_237 = true := by
  decide +kernel

theorem certs110_238 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_238 = true := by
  decide +kernel

theorem certs110_239 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_239 = true := by
  decide +kernel

end Collatz
