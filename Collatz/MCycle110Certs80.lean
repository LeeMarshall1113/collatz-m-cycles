import Collatz.MCycle110Certs79

/-!
# Certificates of the listed shapes of `data110`, chunks 316..319
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_316 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_316 = true := by
  decide +kernel

theorem certs110_317 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_317 = true := by
  decide +kernel

theorem certs110_318 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_318 = true := by
  decide +kernel

theorem certs110_319 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_319 = true := by
  decide +kernel

end Collatz
