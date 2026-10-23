import Collatz.MCycle110Certs21

/-!
# Certificates of the listed shapes of `data110`, chunks 84..87
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_84 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_84 = true := by
  decide +kernel

theorem certs110_85 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_85 = true := by
  decide +kernel

theorem certs110_86 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_86 = true := by
  decide +kernel

theorem certs110_87 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_87 = true := by
  decide +kernel

end Collatz
