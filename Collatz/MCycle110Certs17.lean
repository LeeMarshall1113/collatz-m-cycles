import Collatz.MCycle110Certs16

/-!
# Certificates of the listed shapes of `data110`, chunks 64..67
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_64 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_64 = true := by
  decide +kernel

theorem certs110_65 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_65 = true := by
  decide +kernel

theorem certs110_66 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_66 = true := by
  decide +kernel

theorem certs110_67 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_67 = true := by
  decide +kernel

end Collatz
