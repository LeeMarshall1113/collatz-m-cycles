import Collatz.MCycle110Certs98

/-!
# Certificates of the listed shapes of `data110`, chunks 392..395
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_392 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_392 = true := by
  decide +kernel

theorem certs110_393 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_393 = true := by
  decide +kernel

theorem certs110_394 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_394 = true := by
  decide +kernel

theorem certs110_395 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_395 = true := by
  decide +kernel

end Collatz
