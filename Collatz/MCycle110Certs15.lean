import Collatz.MCycle110Certs14

/-!
# Certificates of the listed shapes of `data110`, chunks 56..59
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_56 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_56 = true := by
  decide +kernel

theorem certs110_57 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_57 = true := by
  decide +kernel

theorem certs110_58 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_58 = true := by
  decide +kernel

theorem certs110_59 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_59 = true := by
  decide +kernel

end Collatz
