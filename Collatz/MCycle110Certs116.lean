import Collatz.MCycle110Certs115

/-!
# Certificates of the listed shapes of `data110`, chunks 460..460
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_460 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_460 = true := by
  decide +kernel

end Collatz
