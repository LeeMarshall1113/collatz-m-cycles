import Collatz.MCycle110Certs65

/-!
# Certificates of the listed shapes of `data110`, chunks 260..263
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_260 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_260 = true := by
  decide +kernel

theorem certs110_261 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_261 = true := by
  decide +kernel

theorem certs110_262 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_262 = true := by
  decide +kernel

theorem certs110_263 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_263 = true := by
  decide +kernel

end Collatz
