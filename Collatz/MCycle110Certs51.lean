import Collatz.MCycle110Certs50

/-!
# Certificates of the listed shapes of `data110`, chunks 200..203
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_200 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_200 = true := by
  decide +kernel

theorem certs110_201 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_201 = true := by
  decide +kernel

theorem certs110_202 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_202 = true := by
  decide +kernel

theorem certs110_203 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_203 = true := by
  decide +kernel

end Collatz
