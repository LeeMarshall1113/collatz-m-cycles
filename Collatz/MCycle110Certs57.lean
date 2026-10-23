import Collatz.MCycle110Certs56

/-!
# Certificates of the listed shapes of `data110`, chunks 224..227
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_224 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_224 = true := by
  decide +kernel

theorem certs110_225 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_225 = true := by
  decide +kernel

theorem certs110_226 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_226 = true := by
  decide +kernel

theorem certs110_227 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_227 = true := by
  decide +kernel

end Collatz
