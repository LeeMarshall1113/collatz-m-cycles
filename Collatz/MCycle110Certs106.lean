import Collatz.MCycle110Certs105

/-!
# Certificates of the listed shapes of `data110`, chunks 420..423
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_420 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_420 = true := by
  decide +kernel

theorem certs110_421 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_421 = true := by
  decide +kernel

theorem certs110_422 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_422 = true := by
  decide +kernel

theorem certs110_423 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_423 = true := by
  decide +kernel

end Collatz
