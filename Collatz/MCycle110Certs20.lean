import Collatz.MCycle110Certs19

/-!
# Certificates of the listed shapes of `data110`, chunks 76..79
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_76 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_76 = true := by
  decide +kernel

theorem certs110_77 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_77 = true := by
  decide +kernel

theorem certs110_78 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_78 = true := by
  decide +kernel

theorem certs110_79 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_79 = true := by
  decide +kernel

end Collatz
