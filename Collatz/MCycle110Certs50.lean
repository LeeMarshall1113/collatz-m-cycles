import Collatz.MCycle110Certs49

/-!
# Certificates of the listed shapes of `data110`, chunks 196..199
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_196 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_196 = true := by
  decide +kernel

theorem certs110_197 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_197 = true := by
  decide +kernel

theorem certs110_198 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_198 = true := by
  decide +kernel

theorem certs110_199 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_199 = true := by
  decide +kernel

end Collatz
