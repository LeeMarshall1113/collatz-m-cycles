import Collatz.MCycle110Certs28

/-!
# Certificates of the listed shapes of `data110`, chunks 112..115
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_112 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_112 = true := by
  decide +kernel

theorem certs110_113 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_113 = true := by
  decide +kernel

theorem certs110_114 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_114 = true := by
  decide +kernel

theorem certs110_115 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_115 = true := by
  decide +kernel

end Collatz
