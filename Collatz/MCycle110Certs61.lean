import Collatz.MCycle110Certs60

/-!
# Certificates of the listed shapes of `data110`, chunks 240..243
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_240 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_240 = true := by
  decide +kernel

theorem certs110_241 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_241 = true := by
  decide +kernel

theorem certs110_242 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_242 = true := by
  decide +kernel

theorem certs110_243 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_243 = true := by
  decide +kernel

end Collatz
