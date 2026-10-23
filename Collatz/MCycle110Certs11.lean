import Collatz.MCycle110Certs10

/-!
# Certificates of the listed shapes of `data110`, chunks 40..43
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_40 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_40 = true := by
  decide +kernel

theorem certs110_41 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_41 = true := by
  decide +kernel

theorem certs110_42 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_42 = true := by
  decide +kernel

theorem certs110_43 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_43 = true := by
  decide +kernel

end Collatz
