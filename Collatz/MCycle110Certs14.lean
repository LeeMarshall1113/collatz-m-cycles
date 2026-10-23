import Collatz.MCycle110Certs13

/-!
# Certificates of the listed shapes of `data110`, chunks 52..55
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_52 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_52 = true := by
  decide +kernel

theorem certs110_53 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_53 = true := by
  decide +kernel

theorem certs110_54 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_54 = true := by
  decide +kernel

theorem certs110_55 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_55 = true := by
  decide +kernel

end Collatz
