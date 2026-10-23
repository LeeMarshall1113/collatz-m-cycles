import Collatz.MCycle110Certs2

/-!
# Certificates of the listed shapes of `data110`, chunks 8..11
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_8 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_8 = true := by
  decide +kernel

theorem certs110_9 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_9 = true := by
  decide +kernel

theorem certs110_10 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_10 = true := by
  decide +kernel

theorem certs110_11 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_11 = true := by
  decide +kernel

end Collatz
