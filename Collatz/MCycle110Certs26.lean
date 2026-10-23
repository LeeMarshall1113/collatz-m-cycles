import Collatz.MCycle110Certs25

/-!
# Certificates of the listed shapes of `data110`, chunks 100..103
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_100 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_100 = true := by
  decide +kernel

theorem certs110_101 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_101 = true := by
  decide +kernel

theorem certs110_102 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_102 = true := by
  decide +kernel

theorem certs110_103 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_103 = true := by
  decide +kernel

end Collatz
