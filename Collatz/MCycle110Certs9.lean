import Collatz.MCycle110Certs8

/-!
# Certificates of the listed shapes of `data110`, chunks 32..35
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_32 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_32 = true := by
  decide +kernel

theorem certs110_33 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_33 = true := by
  decide +kernel

theorem certs110_34 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_34 = true := by
  decide +kernel

theorem certs110_35 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_35 = true := by
  decide +kernel

end Collatz
