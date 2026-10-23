import Collatz.MCycle110Certs15

/-!
# Certificates of the listed shapes of `data110`, chunks 60..63
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_60 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_60 = true := by
  decide +kernel

theorem certs110_61 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_61 = true := by
  decide +kernel

theorem certs110_62 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_62 = true := by
  decide +kernel

theorem certs110_63 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_63 = true := by
  decide +kernel

end Collatz
