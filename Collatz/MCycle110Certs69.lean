import Collatz.MCycle110Certs68

/-!
# Certificates of the listed shapes of `data110`, chunks 272..275
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_272 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_272 = true := by
  decide +kernel

theorem certs110_273 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_273 = true := by
  decide +kernel

theorem certs110_274 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_274 = true := by
  decide +kernel

theorem certs110_275 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_275 = true := by
  decide +kernel

end Collatz
