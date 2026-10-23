import Collatz.MCycle110Certs39

/-!
# Certificates of the listed shapes of `data110`, chunks 156..159
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_156 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_156 = true := by
  decide +kernel

theorem certs110_157 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_157 = true := by
  decide +kernel

theorem certs110_158 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_158 = true := by
  decide +kernel

theorem certs110_159 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_159 = true := by
  decide +kernel

end Collatz
