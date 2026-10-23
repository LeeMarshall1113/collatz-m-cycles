import Collatz.MCycle110Certs11

/-!
# Certificates of the listed shapes of `data110`, chunks 44..47
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_44 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_44 = true := by
  decide +kernel

theorem certs110_45 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_45 = true := by
  decide +kernel

theorem certs110_46 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_46 = true := by
  decide +kernel

theorem certs110_47 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_47 = true := by
  decide +kernel

end Collatz
