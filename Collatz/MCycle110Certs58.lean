import Collatz.MCycle110Certs57

/-!
# Certificates of the listed shapes of `data110`, chunks 228..231
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_228 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_228 = true := by
  decide +kernel

theorem certs110_229 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_229 = true := by
  decide +kernel

theorem certs110_230 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_230 = true := by
  decide +kernel

theorem certs110_231 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_231 = true := by
  decide +kernel

end Collatz
