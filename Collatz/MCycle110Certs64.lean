import Collatz.MCycle110Certs63

/-!
# Certificates of the listed shapes of `data110`, chunks 252..255
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_252 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_252 = true := by
  decide +kernel

theorem certs110_253 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_253 = true := by
  decide +kernel

theorem certs110_254 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_254 = true := by
  decide +kernel

theorem certs110_255 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_255 = true := by
  decide +kernel

end Collatz
