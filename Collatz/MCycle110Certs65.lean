import Collatz.MCycle110Certs64

/-!
# Certificates of the listed shapes of `data110`, chunks 256..259
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_256 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_256 = true := by
  decide +kernel

theorem certs110_257 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_257 = true := by
  decide +kernel

theorem certs110_258 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_258 = true := by
  decide +kernel

theorem certs110_259 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_259 = true := by
  decide +kernel

end Collatz
