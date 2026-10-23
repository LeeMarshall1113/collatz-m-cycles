import Collatz.MCycle110Certs18

/-!
# Certificates of the listed shapes of `data110`, chunks 72..75
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_72 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_72 = true := by
  decide +kernel

theorem certs110_73 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_73 = true := by
  decide +kernel

theorem certs110_74 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_74 = true := by
  decide +kernel

theorem certs110_75 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_75 = true := by
  decide +kernel

end Collatz
