import Collatz.MCycle110Certs31

/-!
# Certificates of the listed shapes of `data110`, chunks 124..127
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_124 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_124 = true := by
  decide +kernel

theorem certs110_125 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_125 = true := by
  decide +kernel

theorem certs110_126 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_126 = true := by
  decide +kernel

theorem certs110_127 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_127 = true := by
  decide +kernel

end Collatz
