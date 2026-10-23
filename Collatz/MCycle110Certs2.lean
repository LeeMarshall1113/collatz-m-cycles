import Collatz.MCycle110Certs1

/-!
# Certificates of the listed shapes of `data110`, chunks 4..7
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_4 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_4 = true := by
  decide +kernel

theorem certs110_5 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_5 = true := by
  decide +kernel

theorem certs110_6 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_6 = true := by
  decide +kernel

theorem certs110_7 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_7 = true := by
  decide +kernel

end Collatz
