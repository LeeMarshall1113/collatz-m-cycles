import Collatz.MCycle110Certs17

/-!
# Certificates of the listed shapes of `data110`, chunks 68..71
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_68 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_68 = true := by
  decide +kernel

theorem certs110_69 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_69 = true := by
  decide +kernel

theorem certs110_70 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_70 = true := by
  decide +kernel

theorem certs110_71 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_71 = true := by
  decide +kernel

end Collatz
