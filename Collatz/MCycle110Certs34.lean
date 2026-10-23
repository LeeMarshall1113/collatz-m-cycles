import Collatz.MCycle110Certs33

/-!
# Certificates of the listed shapes of `data110`, chunks 132..135
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_132 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_132 = true := by
  decide +kernel

theorem certs110_133 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_133 = true := by
  decide +kernel

theorem certs110_134 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_134 = true := by
  decide +kernel

theorem certs110_135 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_135 = true := by
  decide +kernel

end Collatz
