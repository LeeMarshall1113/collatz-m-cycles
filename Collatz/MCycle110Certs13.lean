import Collatz.MCycle110Certs12

/-!
# Certificates of the listed shapes of `data110`, chunks 48..51
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_48 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_48 = true := by
  decide +kernel

theorem certs110_49 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_49 = true := by
  decide +kernel

theorem certs110_50 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_50 = true := by
  decide +kernel

theorem certs110_51 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_51 = true := by
  decide +kernel

end Collatz
